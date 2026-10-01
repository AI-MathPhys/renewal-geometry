/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactSlowExpansion
import RenewalGeometry.Gravity.ExactNormalCoordinatesChart

/-!
# Necessary slow compatibility of bounded-rate limits
  (`thm:supp-exact-five-compatibility`; emergent-spacetime manuscript)

General machinery:
* `SlowCompatibility.exists_tendstoUniformlyOn_subseq`: Arzelà–Ascoli on `[0, T]` for
  uniformly bounded, uniformly Lipschitz families with values in a proper normed space.
* `SlowCompatibility.tendstoUniformlyOn_comp`: composing a uniformly convergent, uniformly
  bounded family with a continuous map of a proper space preserves uniform convergence.

The record.  Exact histories in the chart are solutions `v_j` of the unbalanced field
(`eq:supp-exact-unbalanced-field`) on the rapid-time interval `[0, T/a_j²]`
(`0 ≤ t ≤ T a_j`); their slow form `ξ_j(τ) = a_j⁻¹ v_j(τ/a_j²)` solves the slow system by
`lem:supp-exact-slow-expansion` (`ExactSlowExpansion.slow_expansion`, proved).  Under the
bounded-rate hypothesis `eq:supp-exact-bounded-slow-rate` (on the actual derivative
`derivWithin ξ_j [0,T]`), `five_compatibility` proves: a uniformly convergent subsequence exists;
every uniformly convergent subsequence has a Lipschitz limit `ξ₀` with `Φ₀(ξ₀) = 0` and
`𝔆_sl(ξ₀) = 0` on all of `[0, T]`, and `(x₀)_τ = b_s + Σ₀(ξ₀)` at every interior time (hence
almost everywhere).  The weak decomposition `eq:supp-exact-weak-decomposition` and the coupling
test `p_H C_red = 0` are hypotheses, as in `prop:supp-exact-slow-rank`.
-/

open Filter Set
open scoped Topology NNReal BoundedContinuousFunction

namespace RenewalGeometry
namespace SlowCompatibility

/-! ### Arzelà–Ascoli and uniform composition -/

section General

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup G]

/-- **Arzelà–Ascoli on `[0, T]`.**  A sequence of maps `ℝ → V` (`V` proper) which are bounded
by `M` and `L`-Lipschitz on `[0, T]` has a subsequence converging uniformly on `[0, T]`. -/
theorem exists_tendstoUniformlyOn_subseq {T M L : ℝ} (f : ℕ → ℝ → V)
    (hb : ∀ n, ∀ τ ∈ Icc 0 T, ‖f n τ‖ ≤ M)
    (hL : ∀ n, ∀ τ ∈ Icc 0 T, ∀ σ ∈ Icc 0 T, ‖f n τ - f n σ‖ ≤ L * |τ - σ|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → V,
      TendstoUniformlyOn (fun n => f (φ n)) g atTop (Icc 0 T) := by
  set X := Icc (0 : ℝ) T
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp isCompact_Icc
  set K : ℝ≥0 := Real.toNNReal L
  have hLip : ∀ n, LipschitzWith K (fun x : X => f n x) := fun n =>
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, Subtype.dist_eq, Real.dist_eq]
      exact (hL n x x.2 y y.2).trans
        (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (abs_nonneg _))
  let F : ℕ → X →ᵇ V := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x => f n x, (hLip n).continuous⟩
  let A : Set (X →ᵇ V) := Set.range F
  have hA : Equicontinuous ((↑) : A → X → V) := by
    apply (LipschitzWith.uniformEquicontinuous _ K ?_).equicontinuous
    intro a
    obtain ⟨n, hn⟩ := a.property
    rw [← hn]
    exact hLip n
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : V) M)
      (isCompact_closedBall 0 M) A
      (by
        intro a x ha
        obtain ⟨n, rfl⟩ := ha
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hb n x x.2) hA
  obtain ⟨g, _, φ, hφ, hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  have huni : TendstoUniformly (fun n => F (φ n)) g atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  refine ⟨φ, hφ, fun τ => if h : τ ∈ X then g ⟨τ, h⟩ else 0, ?_⟩
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hg : ((fun τ => if h : τ ∈ X then g ⟨τ, h⟩ else 0) ∘ ((↑) : X → ℝ)) = g := by
    funext x; simp [x.2]
  rw [hg]
  exact huni

/-- Composition of a uniformly convergent family, bounded by `M`, with a continuous map on a
proper space is uniformly convergent. -/
theorem tendstoUniformlyOn_comp {f : V → G} (hf : Continuous f) {M : ℝ} {s : Set ℝ}
    {F : ℕ → ℝ → V} {F₀ : ℝ → V} (hF : TendstoUniformlyOn F F₀ atTop s)
    (hb : ∀ n, ∀ τ ∈ s, ‖F n τ‖ ≤ M) (hb₀ : ∀ τ ∈ s, ‖F₀ τ‖ ≤ M) :
    TendstoUniformlyOn (fun n τ => f (F n τ)) (fun τ => f (F₀ τ)) atTop s := by
  have huc : UniformContinuousOn f (Metric.closedBall 0 M) :=
    (isCompact_closedBall 0 M).uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := huc ε hε
  filter_upwards [hF δ hδ] with n hn τ hτ
  exact hδε _ (by simpa using hb₀ τ hτ) _ (by simpa using hb n τ hτ) (hn τ hτ)

end General

/-! ### Continuity of the slow coefficients -/

section Coefficients

open ExactSlowExpansion

variable {Xs W : Type*} [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [CompleteSpace Xs]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

theorem continuous_sigma0 (Rs : ℝ × (Xs × W) → Xs) : Continuous (sigma0 Rs) := by
  have hd : Continuous fun ξ : Xs × W => slowDir ξ := by
    unfold slowDir; fun_prop
  unfold sigma0
  refine Continuous.add (continuous_const.smul ?_) (continuous_const.smul ?_)
  · refine (iteratedFDeriv ℝ 3 Rs 0).coe_continuous.comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp [hd, continuous_const]
  · refine (iteratedFDeriv ℝ 3 Rs 0).coe_continuous.comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp [hd, continuous_const]

theorem continuous_phi1 (Rf : ℝ × (Xs × W) → W) : Continuous (phi1 Rf) := by
  have hd : Continuous fun ξ : Xs × W => slowDir ξ := by
    unfold slowDir; fun_prop
  unfold phi1
  refine Continuous.add ?_ (continuous_const.smul ?_)
  · refine (iteratedFDeriv ℝ 2 Rf 0).coe_continuous.comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp [hd, continuous_const]
  · refine (iteratedFDeriv ℝ 2 Rf 0).coe_continuous.comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp [hd, continuous_const]

end Coefficients

/-! ### The bounded-rate limit -/

section Record

open ExactSlowExpansion ExactSlowBranch

variable {Xs W Zg Hs : Type*} [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [FiniteDimensional ℝ Xs]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]

/-- The slow form `ξ(τ) = a⁻¹ v(τ/a²)` of a rapid-time history `v` (`t = aτ = a³s`). -/
noncomputable def slowForm (a : ℝ) (v : ℝ → Xs × W) (τ : ℝ) : Xs × W := a⁻¹ • v (τ / a ^ 2)

/-- The principal balance `eq:supp-exact-slow-principal-balance`:
`Φ₀(ξ) = a² z_τ - aΦ₁(ξ) - a²(b_w + Φ₂(a, ξ))` with `z_τ` the weak slow rate. -/
theorem principal_balance (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (bs : Xs) (bw : W)
    (Rs : ℝ × (Xs × W) → Xs) (Rf : ℝ × (Xs × W) → W) {b : ℝ} (hb : b ≠ 0) (ξ : Xs × W) :
    leadingConstraint Cred B ξ = (b ^ 2) • (slowField Cred B bs bw Rs Rf b ξ).2
      - b • phi1 Rf ξ - (b ^ 2) • (bw + phi2 Rf b ξ) := by
  have h1 : b ^ 2 * (b ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hb)
  have h2 : b ^ 2 * b⁻¹ = b := by field_simp
  simp only [slowField, smul_add, smul_smul, h1, h2, one_smul]
  abel

/-- **`thm:supp-exact-five-compatibility`** (bounded-rate limits).  Let `a_j > 0`, `a_j → 0`,
and let `v_j` be exact histories of the unbalanced field (`eq:supp-exact-unbalanced-field`, with
analytic remainders obeying `eq:supp-exact-graded-remainders`) on the rapid-time interval
`[0, T/a_j²]`, i.e. on `0 ≤ t ≤ T a_j`.  Let `ξ_j(τ) = a_j⁻¹ v_j(τ/a_j²)` be their slow form and
assume the bounded slow rate `eq:supp-exact-bounded-slow-rate`
`sup_j sup_τ (|ξ_j(τ)| + |∂_τ ξ_j(τ)|) ≤ M`.  Under the weak decomposition with `p_H C_red = 0`:
* a uniformly convergent subsequence exists (Arzelà–Ascoli);
* every uniformly convergent subsequence has an `M`-Lipschitz limit `ξ₀ = (x₀, z₀)` with
  `Φ₀(ξ₀) = 0` and `𝔆_sl(ξ₀) = 0` on `[0, T]` and `(x₀)_τ = b_s + Σ₀(ξ₀)` at every interior time
  (`eq:supp-exact-five-identities`). -/
theorem five_compatibility (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (bs : Xs) (bw : W)
    (Rs : ℝ × (Xs × W) → Xs) (Rf : ℝ × (Xs × W) → W)
    (hRs : AnalyticAt ℝ Rs 0) (hRf : AnalyticAt ℝ Rf 0)
    (hbs : ∃ δ > 0, ∃ C, ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rs (a, v)‖ ≤ C * (a ^ 4 + a ^ 2 * ‖v‖ + a * ‖v‖ ^ 2))
    (hbf : ∃ δ > 0, ∃ C, ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rf (a, v)‖ ≤ C * (a ^ 4 + a * ‖v‖ + ‖v‖ ^ 2))
    {Jg : Zg →L[ℝ] W} {JH : Hs →L[ℝ] W} {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs}
    (hD : WeakDecomposition B Jg JH pg pH) (hHC : ∀ x, pH (Cred x) = 0)
    {T : ℝ} (hT : 0 < T) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (ha0 : Tendsto a atTop (𝓝 0))
    (v : ℕ → ℝ → Xs × W)
    (hv : ∀ j, ∀ s ∈ Icc 0 (T / a j ^ 2), HasDerivWithinAt (v j)
      (unbalancedField Cred B bs bw Rs Rf (a j) (v j s)) (Icc 0 (T / a j ^ 2)) s)
    (M : ℝ) (hM : ∀ j, ∀ τ ∈ Icc 0 T, ‖slowForm (a j) (v j) τ‖
      + ‖derivWithin (slowForm (a j) (v j)) (Icc 0 T) τ‖ ≤ M) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ξ₀ : ℝ → Xs × W,
      TendstoUniformlyOn (fun n => slowForm (a (φ n)) (v (φ n))) ξ₀ atTop (Icc 0 T)) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ξ₀ : ℝ → Xs × W,
      TendstoUniformlyOn (fun n => slowForm (a (φ n)) (v (φ n))) ξ₀ atTop (Icc 0 T) →
      (∀ τ ∈ Icc 0 T, ∀ σ ∈ Icc 0 T, ‖ξ₀ τ - ξ₀ σ‖ ≤ M * |τ - σ|) ∧
      (∀ τ ∈ Icc 0 T, leadingConstraint Cred B (ξ₀ τ) = 0) ∧
      (∀ τ ∈ Ioo 0 T, HasDerivAt (fun τ => (ξ₀ τ).1) (bs + sigma0 Rs (ξ₀ τ)) τ) ∧
      (∀ τ ∈ Icc 0 T, slowConstraint pg pH Cred bs (sigma0 Rs) (phi1 Rf) (ξ₀ τ) = 0) := by
  set ξ : ℕ → ℝ → Xs × W := fun j => slowForm (a j) (v j) with hξdef
  have hder : ∀ j, ∀ τ ∈ Icc 0 T, HasDerivWithinAt (ξ j)
      (slowField Cred B bs bw Rs Rf (a j) (ξ j τ)) (Icc 0 T) τ := fun j =>
    slow_system_of_unbalanced Cred B bs bw Rs Rf (ha j).ne' (v j) (hv j)
  have hdw : ∀ j, ∀ τ ∈ Icc 0 T, derivWithin (ξ j) (Icc 0 T) τ
      = slowField Cred B bs bw Rs Rf (a j) (ξ j τ) := fun j τ hτ =>
    (hder j τ hτ).derivWithin (uniqueDiffOn_Icc hT τ hτ)
  have hbξ : ∀ j, ∀ τ ∈ Icc 0 T, ‖ξ j τ‖ ≤ M := fun j τ hτ => by
    have := hM j τ hτ; linarith [norm_nonneg (derivWithin (slowForm (a j) (v j)) (Icc 0 T) τ)]
  have hbd : ∀ j, ∀ τ ∈ Icc 0 T, ‖slowField Cred B bs bw Rs Rf (a j) (ξ j τ)‖ ≤ M :=
    fun j τ hτ => by
      have := hM j τ hτ; rw [← hdw j τ hτ]; linarith [norm_nonneg (ξ j τ)]
  have hLipj : ∀ j, ∀ τ ∈ Icc 0 T, ∀ σ ∈ Icc 0 T, ‖ξ j τ - ξ j σ‖ ≤ M * |τ - σ| := by
    intro j τ hτ σ hσ
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (hder j) (hbd j)
      (convex_Icc 0 T) hσ hτ
    rwa [Real.norm_eq_abs] at this
  refine ⟨exists_tendstoUniformlyOn_subseq ξ hbξ hLipj, ?_⟩
  intro φ hφ ξ₀ hconv
  set b : ℕ → ℝ := fun n => a (φ n) with hbdef
  have hb0 : Tendsto b atTop (𝓝 0) := ha0.comp hφ.tendsto_atTop
  have hbpos : ∀ n, 0 < b n := fun n => ha (φ n)
  have hpt : ∀ τ ∈ Icc 0 T, Tendsto (fun n => ξ (φ n) τ) atTop (𝓝 (ξ₀ τ)) :=
    fun τ hτ => hconv.tendsto_at hτ
  have hb₀ : ∀ τ ∈ Icc 0 T, ‖ξ₀ τ‖ ≤ M := fun τ hτ =>
    le_of_tendsto (hpt τ hτ).norm (Eventually.of_forall fun n => hbξ _ τ hτ)
  -- (1) Lipschitz limit
  have hLip0 : ∀ τ ∈ Icc 0 T, ∀ σ ∈ Icc 0 T, ‖ξ₀ τ - ξ₀ σ‖ ≤ M * |τ - σ| := by
    intro τ hτ σ hσ
    exact le_of_tendsto ((hpt τ hτ).sub (hpt σ hσ)).norm
      (Eventually.of_forall fun n => hLipj _ τ hτ σ hσ)
  have hcont0 : ContinuousOn ξ₀ (Icc 0 T) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal M) fun x hx y hy => ?_).continuousOn
    rw [dist_eq_norm, Real.dist_eq]
    exact (hLip0 x hx y hy).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal M) (abs_nonneg _))
  -- uniform bounds on the remainders and on `Φ₁`
  obtain ⟨a₀, ha₀, K, hK⟩ := remainders_bounded hRs hRf hbs hbf M
  obtain ⟨K₁, hK₁⟩ := (isCompact_closedBall (0 : Xs × W) M).exists_bound_of_continuousOn
    (continuous_phi1 Rf).continuousOn
  have hsmall : ∀ᶠ n in atTop, b n < a₀ := hb0.eventually (eventually_lt_nhds ha₀)
  have hmemB : ∀ n, ∀ τ ∈ Icc 0 T, ξ (φ n) τ ∈ Metric.closedBall (0 : Xs × W) M :=
    fun n τ hτ => by rw [Metric.mem_closedBall, dist_zero_right]; exact hbξ _ τ hτ
  -- (2) `Φ₀(ξ₀) = 0`
  have hΦ0 : ∀ τ ∈ Icc 0 T, leadingConstraint Cred B (ξ₀ τ) = 0 := by
    intro τ hτ
    have hlim1 : Tendsto (fun n => leadingConstraint Cred B (ξ (φ n) τ)) atTop
        (𝓝 (leadingConstraint Cred B (ξ₀ τ))) :=
      ((leadingConstraint Cred B).continuous.tendsto _).comp (hpt τ hτ)
    have hg : Tendsto (fun n => b n ^ 2 * (M + ‖bw‖ + K) + b n * K₁) atTop (𝓝 0) := by
      have := ((hb0.pow 2).mul_const (M + ‖bw‖ + K)).add (hb0.mul_const K₁)
      simpa using this
    have hlim2 : Tendsto (fun n => leadingConstraint Cred B (ξ (φ n) τ)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [hsmall] with n hn
      rw [principal_balance Cred B bs bw Rs Rf (hbpos n).ne']
      have hz : ‖(slowField Cred B bs bw Rs Rf (b n) (ξ (φ n) τ)).2‖ ≤ M :=
        (norm_snd_le _).trans (hbd _ τ hτ)
      have hr := (hK (b n) (hbpos n) hn (ξ (φ n) τ) (hbξ _ τ hτ)).2
      have h1 := hK₁ _ (hmemB n τ hτ)
      have hbn := (hbpos n).le
      calc ‖(b n ^ 2) • (slowField Cred B bs bw Rs Rf (b n) (ξ (φ n) τ)).2
            - b n • phi1 Rf (ξ (φ n) τ) - (b n ^ 2) • (bw + phi2 Rf (b n) (ξ (φ n) τ))‖
          ≤ ‖(b n ^ 2) • (slowField Cred B bs bw Rs Rf (b n) (ξ (φ n) τ)).2‖
            + ‖b n • phi1 Rf (ξ (φ n) τ)‖ + ‖(b n ^ 2) • (bw + phi2 Rf (b n) (ξ (φ n) τ))‖ :=
            norm_sub_le_of_le (norm_sub_le _ _) le_rfl
        _ ≤ b n ^ 2 * M + b n * K₁ + b n ^ 2 * (‖bw‖ + K) := by
            rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ b n ^ 2), abs_of_nonneg hbn]
            gcongr
            exact (norm_add_le _ _).trans (by linarith)
        _ = b n ^ 2 * (M + ‖bw‖ + K) + b n * K₁ := by ring
    exact tendsto_nhds_unique hlim1 hlim2
  -- (3) `𝔪(ξ₀) = 0`
  have hpHΦ0 : ∀ ζ, pH (leadingConstraint Cred B ζ) = 0 := fun ζ => by
    simp [hHC, hD.pH_B]
  have hmean : ∀ τ ∈ Icc 0 T, slowMean pH (phi1 Rf) (ξ₀ τ) = 0 := by
    intro τ hτ
    have hlim1 : Tendsto (fun n => pH (phi1 Rf (ξ (φ n) τ))) atTop
        (𝓝 (pH (phi1 Rf (ξ₀ τ)))) :=
      ((pH.continuous.comp (continuous_phi1 Rf)).tendsto _).comp (hpt τ hτ)
    have hg : Tendsto (fun n => b n * (‖pH‖ * (M + (‖bw‖ + K)))) atTop (𝓝 0) := by
      simpa using hb0.mul_const (‖pH‖ * (M + (‖bw‖ + K)))
    have hlim2 : Tendsto (fun n => pH (phi1 Rf (ξ (φ n) τ))) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [hsmall] with n hn
      set ζ := ξ (φ n) τ
      set z' := (slowField Cred B bs bw Rs Rf (b n) ζ).2
      have hbne := (hbpos n).ne'
      have hbal := congrArg pH (principal_balance Cred B bs bw Rs Rf hbne ζ)
      rw [hpHΦ0, map_sub, map_sub, map_smul, map_smul, map_smul] at hbal
      have heq : pH (phi1 Rf ζ) = b n • (pH z' - pH (bw + phi2 Rf (b n) ζ)) := by
        apply smul_right_injective _ hbne
        simp only
        rw [smul_smul, ← pow_two, smul_sub]
        rw [sub_sub, eq_comm, sub_eq_zero] at hbal
        rw [← sub_eq_zero]
        have : b n ^ 2 • pH z' = b n • pH (phi1 Rf ζ) + b n ^ 2 • pH (bw + phi2 Rf (b n) ζ) :=
          hbal
        rw [this]; abel
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (hbpos n)]
      refine mul_le_mul_of_nonneg_left ?_ (hbpos n).le
      have hz : ‖z'‖ ≤ M := (norm_snd_le _).trans (hbd _ τ hτ)
      have hr := (hK (b n) (hbpos n) hn ζ (hbξ _ τ hτ)).2
      calc ‖pH z' - pH (bw + phi2 Rf (b n) ζ)‖ = ‖pH (z' - (bw + phi2 Rf (b n) ζ))‖ := by
            rw [map_sub]
        _ ≤ ‖pH‖ * ‖z' - (bw + phi2 Rf (b n) ζ)‖ := pH.le_opNorm _
        _ ≤ ‖pH‖ * (M + (‖bw‖ + K)) := by
            gcongr
            exact (norm_sub_le _ _).trans (add_le_add hz ((norm_add_le _ _).trans
              (by linarith)))
    exact tendsto_nhds_unique hlim1 hlim2
  -- (4) the regular `x` equation at interior times
  have hderiv : ∀ τ ∈ Ioo 0 T, HasDerivAt (fun τ => (ξ₀ τ).1) (bs + sigma0 Rs (ξ₀ τ)) τ := by
    intro τ hτ
    have hconv' : TendstoUniformlyOn (fun n τ => ξ (φ n) τ) ξ₀ atTop (Ioo 0 T) :=
      hconv.mono Ioo_subset_Icc_self
    have hSig : TendstoUniformlyOn (fun n τ => bs + sigma0 Rs (ξ (φ n) τ))
        (fun τ => bs + sigma0 Rs (ξ₀ τ)) atTop (Ioo 0 T) :=
      tendstoUniformlyOn_comp (f := fun ζ => bs + sigma0 Rs ζ)
        (continuous_const.add (continuous_sigma0 Rs)) hconv'
        (fun n τ hτ => hbξ _ τ (Ioo_subset_Icc_self hτ))
        (fun τ hτ => hb₀ τ (Ioo_subset_Icc_self hτ))
    have hf' : TendstoUniformlyOn
        (fun n τ => (slowField Cred B bs bw Rs Rf (b n) (ξ (φ n) τ)).1)
        (fun τ => bs + sigma0 Rs (ξ₀ τ)) atTop (Ioo 0 T) := by
      rw [Metric.tendstoUniformlyOn_iff] at hSig ⊢
      intro ε hε
      have hgb : Tendsto (fun n => b n * K) atTop (𝓝 0) := by simpa using hb0.mul_const K
      filter_upwards [hSig (ε / 2) (half_pos hε), hsmall,
        hgb.eventually (eventually_lt_nhds (half_pos hε))] with n hn hn' hn'' x hx
      have hr := (hK (b n) (hbpos n) hn' (ξ (φ n) x) (hbξ _ x (Ioo_subset_Icc_self hx))).1
      have h1 := hn x hx
      simp only [slowField]
      calc dist (bs + sigma0 Rs (ξ₀ x)) (bs + sigma0 Rs (ξ (φ n) x) + b n • sigma1 Rs (b n) (ξ (φ n) x))
          ≤ dist (bs + sigma0 Rs (ξ₀ x)) (bs + sigma0 Rs (ξ (φ n) x))
            + dist (bs + sigma0 Rs (ξ (φ n) x))
                (bs + sigma0 Rs (ξ (φ n) x) + b n • sigma1 Rs (b n) (ξ (φ n) x)) :=
            dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
            refine add_lt_add_of_lt_of_le h1 ?_
            rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
              abs_of_pos (hbpos n)]
            calc b n * ‖sigma1 Rs (b n) (ξ (φ n) x)‖ ≤ b n * K :=
                  mul_le_mul_of_nonneg_left hr (hbpos n).le
              _ ≤ ε / 2 := hn''.le
        _ = ε := add_halves ε
    have hf : ∀ᶠ n in atTop, ∀ x ∈ Ioo 0 T, HasDerivAt (fun τ => (ξ (φ n) τ).1)
        ((slowField Cred B bs bw Rs Rf (b n) (ξ (φ n) x)).1) x := by
      refine Eventually.of_forall fun n x hx => ?_
      have h := (hder (φ n) x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
      exact (ContinuousLinearMap.fst ℝ Xs W).hasFDerivAt.comp_hasDerivAt x h
    have hfg : ∀ x ∈ Ioo 0 T, Tendsto (fun n => (ξ (φ n) x).1) atTop (𝓝 (ξ₀ x).1) :=
      fun x hx => (continuous_fst.tendsto _).comp (hpt x (Ioo_subset_Icc_self hx))
    exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hf' hf hfg hτ
  -- (5) `𝔤(ξ₀) = 0`: `p_g C_red x₀ = -p_g B z₀ = 0` is constant
  have hgrad_Ioo : EqOn (fun τ => slowGradient pg Cred bs (sigma0 Rs) (ξ₀ τ)) 0 (Ioo 0 T) := by
    intro τ hτ
    have hconst : (fun σ => pg (Cred (ξ₀ σ).1)) =ᶠ[𝓝 τ] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with σ hσ
      have h0 := hΦ0 σ (Ioo_subset_Icc_self hσ)
      rw [leadingConstraint_apply] at h0
      have : Cred (ξ₀ σ).1 = -B (ξ₀ σ).2 := eq_neg_of_add_eq_zero_left h0
      rw [this, map_neg, hD.pg_B, neg_zero]
    have hd1 : HasDerivAt (fun σ => pg (Cred (ξ₀ σ).1)) (pg (Cred (bs + sigma0 Rs (ξ₀ τ)))) τ :=
      (pg.comp Cred).hasFDerivAt.comp_hasDerivAt τ (hderiv τ hτ)
    have hd2 : HasDerivAt (fun σ => pg (Cred (ξ₀ σ).1)) 0 τ :=
      (hasDerivAt_const τ (0 : Zg)).congr_of_eventuallyEq hconst
    exact hd1.unique hd2
  have hgrad : EqOn (fun τ => slowGradient pg Cred bs (sigma0 Rs) (ξ₀ τ)) 0 (Icc 0 T) := by
    refine hgrad_Ioo.of_subset_closure ?_ continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hT.ne])
    have hc : Continuous fun ζ : Xs × W => slowGradient pg Cred bs (sigma0 Rs) ζ := by
      unfold slowGradient
      exact pg.continuous.comp (Cred.continuous.comp (continuous_const.add (continuous_sigma0 Rs)))
    exact hc.comp_continuousOn hcont0
  refine ⟨hLip0, hΦ0, hderiv, fun τ hτ => ?_⟩
  simp only [slowConstraint]
  rw [show slowGradient pg Cred bs (sigma0 Rs) (ξ₀ τ) = 0 from hgrad hτ, hmean τ hτ]
  rfl

/-- Non-vacuity: the hypothesis packet of `five_compatibility` is satisfiable (zero data on
`Xs = ℝ`, `W = ℝ²` with the decomposition `W = 0 ⊕ ℝ ⊕ ℝ`, amplitudes `a_j = 1/(j+1)`). -/
example : True := by
  have hD : WeakDecomposition (0 : ℝ × ℝ →L[ℝ] ℝ × ℝ) (ContinuousLinearMap.inl ℝ ℝ ℝ)
      (ContinuousLinearMap.inr ℝ ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    { pg_Jg := fun _ => rfl, pH_JH := fun _ => rfl, pg_JH := fun _ => rfl,
      pH_Jg := fun _ => rfl, pg_B := fun _ => rfl, pH_B := fun _ => rfl,
      split := fun w => ⟨0, by simp⟩ }
  have := five_compatibility (Xs := ℝ) (W := ℝ × ℝ) (Zg := ℝ) (Hs := ℝ) 0 0 0 0
    (fun _ => 0) (fun _ => 0) analyticAt_const analyticAt_const
    ⟨1, one_pos, 0, fun _ _ _ _ _ => by simp⟩ ⟨1, one_pos, 0, fun _ _ _ _ _ => by simp⟩
    hD (fun _ => by simp) one_pos (fun j => 1 / ((j : ℝ) + 1)) (fun j => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat (fun _ _ => 0)
    (fun j s _ => by
      have h := hasDerivWithinAt_const (𝕜 := ℝ) s (Icc 0 (1 / (1 / ((j : ℝ) + 1)) ^ 2))
        (0 : ℝ × (ℝ × ℝ))
      refine h.congr_deriv ?_
      simp [unbalancedField]
      rfl)
    0 (fun j τ _ => by
      have h0 : slowForm (1 / ((j : ℝ) + 1)) (fun _ => (0 : ℝ × (ℝ × ℝ))) = fun _ => 0 :=
        funext fun _ => by simp [slowForm]
      rw [h0]; simp)
  trivial

end Record

/-! ### Physical readout orders along a bounded-rate history -/

section Readout

open ExactNormalCoordinates

variable {Qs LA LW Xc Rd : Type*}
  [NormedAddCommGroup Qs] [NormedSpace ℝ Qs] [CompleteSpace Qs]
  [NormedAddCommGroup LA] [NormedSpace ℝ LA] [CompleteSpace LA]
  [NormedAddCommGroup LW] [NormedSpace ℝ LW] [CompleteSpace LW]
  [NormedAddCommGroup Xc] [NormedSpace ℝ Xc] [NormedAddCommGroup Rd]

/-- The chart point `(a, w)` of a slow state `ξ = (x, z)`, `x = (q, p_A)`: the balanced free
coordinate is `w = (q, p_A, p_W)` with `p_W = a z` (`w = (x, az)` of
`subsec:supp-exact-slow`). -/
def chartPoint (a : ℝ) (x : Qs × LA) (z : LW) : ℝ × (Qs × (LA × LW)) := (a, (x.1, (x.2, a • z)))

/-- The multiplier coordinates of the chart `eq:supp-exact-normal-chart` at a slow state:
`λ_A = λ⁰_A + a²(p_A - H p_W)`, `λ_W = λ⁰_W + a p_W`, `p_W = a z`. -/
def chartMultipliers (lA0 : LA) (lW0 : LW) (H : LW →L[ℝ] LA) (a : ℝ) (x : Qs × LA) (z : LW) :
    LA × LW :=
  (lA0 + a ^ 2 • (x.2 - H (a • z)), lW0 + a • (a • z))

/-- **Physical velocity orders.**  Along a slow history `ξ(τ) = (x(τ), z(τ))` with slow rates
bounded by `M`, read in physical time `t = aτ` through a chart map `𝒳(a, w)` whose partial
derivatives obey `‖D_q𝒳‖ ≤ K a²`, `‖D_p𝒳‖ ≤ K a⁴` at the history (the orders of
`eq:supp-exact-normal-derivatives`), the physical velocities satisfy
`‖X_t‖ ≤ 2KM a` and `‖λ_t‖ ≤ (1 + ‖H‖) M a`. -/
theorem physical_velocity_orders (𝒳 : ℝ × (Qs × (LA × LW)) → Xc) (lA0 : LA) (lW0 : LW)
    (H : LW →L[ℝ] LA) {a K M τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {x : ℝ → Qs × LA} {z : ℝ → LW} {x' : Qs × LA} {z' : LW}
    (hx : HasDerivAt x x' τ) (hz : HasDerivAt z z' τ) (hx' : ‖x'‖ ≤ M) (hz' : ‖z'‖ ≤ M)
    {D : ℝ × (Qs × (LA × LW)) →L[ℝ] Xc} (hD : HasFDerivAt 𝒳 D (chartPoint a (x τ) (z τ)))
    (hDq : ‖D ∘L iotaQ Qs LA LW‖ ≤ K * a ^ 2) (hDp : ‖D ∘L iotaP Qs LA LW‖ ≤ K * a ^ 4) :
    ∃ Xt : Xc, HasDerivAt (fun t => 𝒳 (chartPoint a (x (t / a)) (z (t / a)))) Xt (a * τ) ∧
      ‖Xt‖ ≤ 2 * K * M * a ∧
    ∃ lt : LA × LW,
      HasDerivAt (fun t => chartMultipliers (Qs := Qs) lA0 lW0 H a (x (t / a)) (z (t / a))) lt
        (a * τ) ∧ ‖lt‖ ≤ (1 + ‖H‖) * M * a := by
  have hane : a ≠ 0 := ha.ne'
  have hτ : a * τ / a = τ := by field_simp
  have hdiv : HasDerivAt (fun t : ℝ => t / a) (1 / a) (a * τ) := (hasDerivAt_id _).div_const a
  have hx0 : HasDerivAt x x' (a * τ / a) := by rw [hτ]; exact hx
  have hz0 : HasDerivAt z z' (a * τ / a) := by rw [hτ]; exact hz
  have hx2 : HasDerivAt (fun t => x (t / a)) ((1 / a) • x') (a * τ) := hx0.scomp (a * τ) hdiv
  have hz2 : HasDerivAt (fun t => z (t / a)) ((1 / a) • z') (a * τ) := hz0.scomp (a * τ) hdiv
  have hM : 0 ≤ M := (norm_nonneg _).trans hx'
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ K * a ^ 2 := (norm_nonneg _).trans hDq
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  -- the chart path and its derivative
  set u : ℝ × (Qs × (LA × LW)) := (0, ((1 / a) • x'.1, ((1 / a) • x'.2, a • (1 / a) • z')))
  have hpath : HasDerivAt (fun t => chartPoint a (x (t / a)) (z (t / a))) u (a * τ) := by
    have h1 := hx2.fst
    have h2 := hx2.snd
    have h3 := hz2.const_smul a
    exact (hasDerivAt_const _ a).prodMk (h1.prodMk (h2.prodMk h3))
  have hu : u = iotaQ Qs LA LW ((1 / a) • x'.1) + iotaP Qs LA LW ((1 / a) • x'.2, a • (1 / a) • z') := by
    simp [u, iotaQ, iotaP]
  refine ⟨D u, ?_, ?_, ?_⟩
  · have e : (fun t => 𝒳 (chartPoint a (x (t / a)) (z (t / a))))
        = 𝒳 ∘ fun t => chartPoint a (x (t / a)) (z (t / a)) := rfl
    rw [e]
    have hD' : HasFDerivAt 𝒳 D (chartPoint a (x (a * τ / a)) (z (a * τ / a))) := by rwa [hτ]
    exact hD'.comp_hasDerivAt (a * τ) hpath
  · rw [hu, map_add]
    have e1 : D (iotaQ Qs LA LW ((1 / a) • x'.1)) = (D ∘L iotaQ Qs LA LW) ((1 / a) • x'.1) := rfl
    have e2 : D (iotaP Qs LA LW ((1 / a) • x'.2, a • (1 / a) • z'))
        = (D ∘L iotaP Qs LA LW) ((1 / a) • x'.2, a • (1 / a) • z') := rfl
    rw [e1, e2]
    have hn1 : ‖(1 / a) • x'.1‖ ≤ M / a := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), one_div, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right ((norm_fst_le x').trans hx') ha.le
    have hn2 : ‖(((1 / a) • x'.2, a • (1 / a) • z') : LA × LW)‖ ≤ M / a := by
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), one_div, inv_mul_eq_div]
        exact div_le_div_of_nonneg_right ((norm_snd_le x').trans hx') ha.le
      · rw [smul_smul, mul_one_div_cancel hane, one_smul]
        exact hz'.trans (le_div_self hM ha ha1)
    calc ‖(D ∘L iotaQ Qs LA LW) ((1 / a) • x'.1)
          + (D ∘L iotaP Qs LA LW) ((1 / a) • x'.2, a • (1 / a) • z')‖
        ≤ K * a ^ 2 * (M / a) + K * a ^ 4 * (M / a) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact ((D ∘L iotaQ Qs LA LW).le_opNorm _).trans
              (mul_le_mul hDq hn1 (norm_nonneg _) (by positivity))
          · exact ((D ∘L iotaP Qs LA LW).le_opNorm _).trans
              (mul_le_mul hDp hn2 (norm_nonneg _) (by positivity))
      _ ≤ K * a ^ 2 * (M / a) + K * a ^ 2 * (M / a) := by
          have : a ^ 4 ≤ a ^ 2 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
          gcongr
      _ = 2 * K * M * a := by field_simp; ring
  · -- multipliers
    have h1 : HasDerivAt (fun t => (x (t / a)).2) ((1 / a) • x'.2) (a * τ) :=
      (ContinuousLinearMap.snd ℝ Qs LA).hasFDerivAt.comp_hasDerivAt _ hx2
    have h2 : HasDerivAt (fun t => H (a • z (t / a))) (H (a • (1 / a) • z')) (a * τ) :=
      H.hasFDerivAt.comp_hasDerivAt _ (hz2.const_smul a)
    have hA : HasDerivAt (fun t => lA0 + a ^ 2 • ((x (t / a)).2 - H (a • z (t / a))))
        (a ^ 2 • ((1 / a) • x'.2 - H (a • (1 / a) • z'))) (a * τ) :=
      HasDerivAt.const_add lA0 (HasDerivAt.const_smul (a ^ 2) (HasDerivAt.sub h1 h2))
    have hW : HasDerivAt (fun t => lW0 + a • (a • z (t / a))) (a • (a • (1 / a) • z')) (a * τ) :=
      ((hz2.const_smul a).const_smul a).const_add lW0
    refine ⟨_, hA.prodMk hW, ?_⟩
    have s1 : a ^ 2 • ((1 / a) • x'.2 - H (a • (1 / a) • z')) = a • (x'.2 - a • H z') := by
      rw [map_smul, map_smul, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
      congr 1 <;> congr 1 <;> field_simp
    have s2 : a • (a • (1 / a) • z') = a • z' := by
      rw [smul_smul a (1 / a), mul_one_div_cancel hane, one_smul]
    rw [s1, s2, Prod.norm_def]
    refine max_le ?_ ?_
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      have : ‖x'.2 - a • H z'‖ ≤ (1 + ‖H‖) * M := by
        calc ‖x'.2 - a • H z'‖ ≤ ‖x'.2‖ + ‖a • H z'‖ := norm_sub_le _ _
          _ ≤ M + ‖H‖ * M := by
              refine add_le_add ((norm_snd_le x').trans hx') ?_
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
              calc a * ‖H z'‖ ≤ 1 * (‖H‖ * ‖z'‖) :=
                    mul_le_mul ha1 (H.le_opNorm z') (norm_nonneg _) zero_le_one
                _ ≤ ‖H‖ * M := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hz' (norm_nonneg _)
          _ = (1 + ‖H‖) * M := by ring
      nlinarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      have : ‖z'‖ ≤ (1 + ‖H‖) * M := hz'.trans (by nlinarith [norm_nonneg H])
      nlinarith

/-- **Physical acceleration order.**  If the physical history satisfies the canonical equation
`X_t = F(X, λ)` near `t₀` and `F` has derivative bounded by `K_F` at `(X(t₀), λ(t₀))`, then
`X_tt = DF[X_t, λ_t]` exists with `‖X_tt‖ ≤ K_F (‖X_t‖ + ‖λ_t‖)`. -/
theorem physical_acceleration_order {Lm : Type*} [NormedAddCommGroup Lm] [NormedSpace ℝ Lm]
    (F : Xc × Lm → Xc) {X : ℝ → Xc} {lam : ℝ → Lm} {t₀ : ℝ} {Xt : Xc} {lt : Lm}
    (hX : HasDerivAt X Xt t₀) (hl : HasDerivAt lam lt t₀)
    {DF : Xc × Lm →L[ℝ] Xc} (hF : HasFDerivAt F DF (X t₀, lam t₀)) {KF : ℝ}
    (hKF : ‖DF‖ ≤ KF) :
    HasDerivAt (fun t => F (X t, lam t)) (DF (Xt, lt)) t₀ ∧
      ‖DF (Xt, lt)‖ ≤ KF * (‖Xt‖ + ‖lt‖) := by
  refine ⟨hF.comp_hasDerivAt t₀ (hX.prodMk hl), ?_⟩
  calc ‖DF (Xt, lt)‖ ≤ ‖DF‖ * ‖(Xt, lt)‖ := DF.le_opNorm _
    _ ≤ KF * (‖Xt‖ + ‖lt‖) := by
        refine mul_le_mul hKF ?_ (norm_nonneg _) ((norm_nonneg _).trans hKF)
        rw [Prod.norm_def]
        exact max_le (le_add_of_nonneg_right (norm_nonneg _))
          (le_add_of_nonneg_left (norm_nonneg _))

/-- **Readout order.**  A readout `ρ` which is `L`-Lipschitz on a set containing the reference
jet `J₀` (with vanishing reference curvature `ρ(J₀) = 0`) and the actual jet `J` satisfies
`‖ρ(J)‖ ≤ L ‖J - J₀‖`; with jets `O(a)`-close to the reference this is the curvature order
`O(a)`. -/
theorem readout_order {Jt : Type*} [NormedAddCommGroup Jt] (ρ : Jt → Rd) {S : Set Jt}
    {L : ℝ≥0} (hρ : LipschitzOnWith L ρ S) {J₀ J : Jt} (h₀ : J₀ ∈ S) (hJ : J ∈ S)
    (hρ₀ : ρ J₀ = 0) : ‖ρ J‖ ≤ L * ‖J - J₀‖ := by
  have := hρ.dist_le_mul J hJ J₀ h₀
  rwa [dist_eq_norm, dist_eq_norm, hρ₀, sub_zero] at this

end Readout

end SlowCompatibility
end RenewalGeometry
