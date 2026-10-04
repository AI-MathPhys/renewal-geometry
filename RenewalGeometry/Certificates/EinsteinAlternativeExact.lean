/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Certificates.CofinalFailureWitness
import RenewalGeometry.Gravity.RenewalEinsteinCertificationExact
import RenewalGeometry.Gravity.CurvatureEnergyPropagationExact
import RenewalGeometry.Gravity.DiscreteCurvatureCertificateExact
import RenewalGeometry.Renewal.EfficientCutConstantScreen
import RenewalGeometry.Renewal.SpatialScreenCutMarginAlternative

/-!
# Einstein limit or failed certificate
  (`thm:main-einstein-alternative`, `subsec:supp-failed-certificates`; emergent-spacetime
  manuscript)

The corollary applies the finite reconstructions and the certification conditions `(E1)`–`(E5)`
of `thm:main-renewal-einstein` to a selected cofinal sequence of finite records: either the
certificates pass on a cofinal tail and a subsequence has the Einstein limit, or the failing
algebraic test, residual, calibrated comparison, positive margin, propagation budget or
compactness tail is retained on the same records with its cofinal witness.

## General infrastructure

* `Certificate` (six kinds: algebraic, residual, budget, margin, compactness tail, calibrated
  comparison) with `Certificate.Passes` (on a cofinal tail), `Certificate.Witness` (the cofinal
  witness of `subsec:supp-failed-certificates`), `Certificate.passes_or_witness` (built on
  `Certificates/CofinalFailureWitness.lean`) and `Certificate.not_passes_of_witness` (the witness
  genuinely obstructs: the alternative is exclusive).
* `trunc`, `tendsto_trunc_iff`: truncated real residuals of extended norms.
* `cauchy_of_screens` (**compact-screen upgrade**): uniformly small tails outside declared screens
  plus Cauchy transported-screen comparisons give a Cauchy comparison in `L²`.
* `exists_l2LocTendsto_of_cauchy` (**completeness of `L²_loc(Ω)`** on an open `Ω ⊆ ℝ^d`, with an
  almost-everywhere convergent diagonal subsequence on a compact exhaustion).
* `ContinuousPropagationRecord.le_of_budgets`, `DiscretePropagationRecord.le_of_budgets`,
  `CurvatureRoute.bounded`: the propagation certificates `thm:main-curvature-propagation` and
  `thm:main-discrete-curvature` (via `curvature_energy_uniform_bound`,
  `derived_l2_curvature_bound`, `discrete_curvature_certificate`) turn bounded initial, growth,
  transfer, source, duration, lapse and interpolation budgets and a positive step margin into a
  uniform curvature bound.

## The certification procedure

`EinsteinCertificationProcedure` carries the records of `thm:main-renewal-einstein` (scores,
coframes, connections, curvature records, Cartan writer `W`, represented torsion, physical lifts,
realized first variations), the standing structure of the regulators (`mt:adm`) and the
regularity of each finite record, and the typed record data the certificates are computed from.
`cert` (common items `Item`), `fullCert` (full-connection route `FullItem`) and
`LiteralLinkRoute.cert` compute one certificate per item of the failure bank:

* common-action curl/period (algebraic; typed defect), realized metric first variation
  (residual), physical first-variation remainder `eq:main-first-variation-reduction` (residual),
  lift consistency with `-½ k g` in `L^∞(K)` (residual) and lift budget;
* calibrated Holst/Palatini/volume coefficients (comparisons), Palatini normalization (margin);
* cut margin `I^eff_X` of the endpoint graphs (margin; `EndpointCutRecord`, computed by
  `FiniteWeightedGraph.efficientCutConstant`);
* face linearity (summability budget; typed defect), memory subtraction (algebraic; typed
  defect), Lorentz naturality of the classified score (algebraic), torsion = spinless connection
  Euler residual on every compact (residual), Cartan nondegeneracy (capped margin);
* initial, growth, transfer, differentiated-source, duration, lapse budgets, curvature
  interpolation stability and reconstruction error, discrete step margin (`CurvatureRoute`);
* Cartan curvature mismatch `𝔠_X` and Cartan/interface incidence mismatch `𝔍_X` (residuals,
  entrywise; the distributional derivative carries all interface contributions), uniform spatial
  `L³` connection budget (the disclosed amendment of `RenewalEinsteinCertification`);
* literal-link chart (algebraic) and energy (budget) on the periodic branch;
* common-cylinder compactness: coframe and connection tails outside declared screens (tails) and
  transported-screen comparisons (comparisons), `L⁶` coframe budget, coframe noncollapse
  (capped margin of `det e_X`).

## Main results

* `EinsteinCertificationProcedure.certification_of_passes`: **passing certificates give the
  packet `RenewalEinsteinCertification` `(E1)`–`(E5)`** along a subsequence, with the limits
  `(e, ω, α, β, λ)` and the lift bounds produced from the certificates.
* `EinsteinCertificationProcedure.einstein_limit_or_failed_certificate`
  (**`thm:main-einstein-alternative`**): `P.Passes` and a subsequence with the Einstein conclusion
  of `thm:main-renewal-einstein` (`EinsteinCertificationConclusion`), or `¬P.Passes` and the
  failure witness `P.FailureWitness`.
* `flatProcedure_passes` (non-vacuity of the positive branch) and `collapsingProcedure_fails`
  (a failing procedure: collapsing endpoint graphs, cut-margin witness).

## Disclosed renderings

The certificates are computed on the common-cylinder interpolants (as in
`RenewalEinsteinCertification`).  Items described in words in the manuscript are typed as data
with their stated properties: the curl/period, memory and face-subdivision defects (real
sequences), the declared transported screens (`ScreenFamily`: measurable, exhausting, nested),
the Cartan writer `W`, the propagation writers and their stable interpolations
(`ContinuousPropagationRecord`, `DiscretePropagationRecord`).  The curl/period, memory, face and
cut-margin certificates are part of `Passes` and of the failure bank but are not used in the
derivation of `(E1)`–`(E5)`: the reconstructed common action enters through its realized first
variations, the classified score through the gravitational class, and the spatial screens
through the declared screens.  On the periodic literal-link route the chart/energy criterion is
computed on the link records and the output of `thm:main-literal-link-compactness` transported to
the common cylinder is the stated property `LiteralLinkRoute.compactness` (the lattice theorem is
proved in its periodic setting; its transport is not formalised, as in the parent packet).  The
selected subsequence starts beyond the cofinal tail on which the margins and algebraic tests pass.
-/

open MeasureTheory Filter Topology ENNReal TopologicalSpace Set
open scoped NNReal Distributions Matrix

noncomputable section

namespace RenewalGeometry.EinsteinAlternative

/-! ### Certificate kinds and their cofinal witnesses -/

/-- One sufficient certificate of the failure bank of `subsec:supp-failed-certificates`, given by
the sequence of finite records it is computed from: a finite algebraic test, a residual that must
tend to zero, a budget that must stay bounded, a positive lower margin, a compactness tail
(`τ n R` = mass of record `n` outside the declared screen of size `R`), or a calibrated Cauchy
comparison of pairs of records. -/
inductive Certificate
  | algebraic (P : ℕ → Prop)
  | residual (r : ℕ → ℝ)
  | budget (b : ℕ → ℝ)
  | margin (μ : ℕ → ℝ)
  | tail (τ : ℕ → ℕ → ℝ)
  | comparison (d : ℕ → ℕ → ℝ)

namespace Certificate

/-- The certificate passes on a cofinal tail of the selected sequence. -/
def Passes : Certificate → Prop
  | algebraic P => ∀ᶠ n in atTop, P n
  | residual r => Tendsto r atTop (𝓝 0)
  | budget b => BddAbove (Set.range b)
  | margin μ => ∃ c > 0, ∀ᶠ n in atTop, c ≤ μ n
  | tail τ => ∀ ε > 0, ∃ R, ∀ n, τ n R ≤ ε
  | comparison d => ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, d m n < ε

/-- The cofinal witness of a failed certificate (`subsec:supp-failed-certificates`): the actual
algebraic defect on cofinally many records; a residual bounded below by `ε > 0` along a
subsequence; a budget tending to infinity along a subsequence; a margin below `1/(k+1)` along a
subsequence; `ε > 0` and arbitrarily late records with mass `> ε` outside arbitrarily large
screens; separated pairs of records along two increasing index sequences. -/
def Witness : Certificate → Prop
  | algebraic P => ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ¬P (φ k)
  | residual r => ∃ ε > 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ε ≤ |r (φ k)|
  | budget b => ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (b ∘ φ) atTop atTop
  | margin μ => ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, μ (φ k) < 1 / ((k : ℝ) + 1)
  | tail τ => ∃ ε > 0, ∀ R N : ℕ, ∃ n ≥ N, ε < τ n R
  | comparison d => ∃ ε > 0, ∃ φ ψ : ℕ → ℕ, StrictMono φ ∧ StrictMono ψ ∧
      ∀ k, ε ≤ d (φ k) (ψ k)

/-- Well-formedness of a certificate: a compactness tail must be individually tight and
antitone in the screen size (declared exhausting, nested screens). -/
def Admissible : Certificate → Prop
  | tail τ => (∀ n, Tendsto (τ n) atTop (𝓝 0)) ∧ ∀ n, Antitone (τ n)
  | _ => True

/-- **Pass-or-witness** for one admissible certificate. -/
theorem passes_or_witness : ∀ c : Certificate, c.Admissible → c.Passes ∨ c.Witness
  | algebraic P, _ => by
      by_cases h : ∀ᶠ n in atTop, P n
      · exact Or.inl h
      · right
        rw [not_eventually] at h
        exact extraction_of_frequently_atTop h
  | residual r, _ => by
      by_cases h : Tendsto r atTop (𝓝 0)
      · exact Or.inl h
      · exact Or.inr (CofinalWitness.exists_subseq_residual_ge_of_not_tendsto h)
  | budget b, _ => by
      by_cases h : BddAbove (Set.range b)
      · exact Or.inl h
      · exact Or.inr (CofinalWitness.exists_subseq_tendsto_atTop_of_not_bddAbove h)
  | margin μ, _ => by
      by_cases h : ∃ c > 0, ∀ᶠ n in atTop, c ≤ μ n
      · exact Or.inl h
      · exact Or.inr (CofinalWitness.exists_subseq_margin_lt_of_not_eventually_ge h)
  | tail τ, hadm => by
      by_cases h : ∀ ε > 0, ∃ R, ∀ n, τ n R ≤ ε
      · exact Or.inl h
      · exact Or.inr (CofinalWitness.exists_late_escape_of_not_uniformly_tight hadm.1 hadm.2 h)
  | comparison d, _ => by
      by_cases h : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, d m n < ε
      · exact Or.inl h
      · exact Or.inr (CofinalWitness.exists_separated_pairs_of_not_cauchy h)

/-- A cofinal witness genuinely obstructs the certificate. -/
theorem not_passes_of_witness : ∀ c : Certificate, c.Witness → ¬c.Passes
  | algebraic P, ⟨φ, hφ, hP⟩, h => by
      obtain ⟨N, hN⟩ := eventually_atTop.1 h
      exact hP N (hN _ (hφ.id_le N))
  | residual r, ⟨ε, hε, φ, hφ, hr⟩, h => by
      have h' : Tendsto (fun k => |r (φ k)|) atTop (𝓝 0) := by
        simpa using (h.comp hφ.tendsto_atTop).abs
      obtain ⟨k, hk⟩ := (h'.eventually (gt_mem_nhds hε)).exists
      exact absurd (hr k) (not_le.2 hk)
  | budget b, ⟨φ, hφ, hb⟩, ⟨M, hM⟩ => by
      obtain ⟨k, hk⟩ := (hb.eventually_gt_atTop M).exists
      exact absurd (hM ⟨φ k, rfl⟩) (not_le.2 hk)
  | margin μ, ⟨φ, hφ, hμ⟩, ⟨c, hc, h⟩ => by
      have h1 := hφ.tendsto_atTop.eventually h
      have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hc)
      obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
      exact absurd (hμ k) (not_lt.2 (hk2.le.trans hk1))
  | tail τ, ⟨ε, hε, hw⟩, h => by
      obtain ⟨R, hR⟩ := h ε hε
      obtain ⟨n, -, hn⟩ := hw R 0
      exact absurd (hR n) (not_le.2 hn)
  | comparison d, ⟨ε, hε, φ, ψ, hφ, hψ, hd⟩, h => by
      obtain ⟨N, hN⟩ := h ε hε
      exact absurd (hN (φ N) (hφ.id_le N) (ψ N) (hψ.id_le N)) (not_lt.2 (hd N))

/-- Exclusive alternative for one admissible certificate. -/
theorem passes_xor_witness (c : Certificate) (hc : c.Admissible) : c.Passes ↔ ¬c.Witness :=
  ⟨fun hp hw => c.not_passes_of_witness hw hp, fun hw => (c.passes_or_witness hc).resolve_right hw⟩

/-- A trivially passing certificate (used for items that do not occur on a given route). -/
def trivial : Certificate := algebraic fun _ => True

theorem trivial_passes : trivial.Passes := Eventually.of_forall fun _ => True.intro

theorem trivial_admissible : trivial.Admissible := True.intro

end Certificate

/-- A family of certificates indexed by `ι`: all pass, or one fails with its cofinal witness. -/
theorem forall_passes_or_exists_witness {ι : Type*} (c : ι → Certificate)
    (hc : ∀ i, (c i).Admissible) : (∀ i, (c i).Passes) ∨ ∃ i, (c i).Witness := by
  by_cases h : ∀ i, (c i).Passes
  · exact Or.inl h
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr ⟨i, ((c i).passes_or_witness (hc i)).resolve_left hi⟩

/-! ### Truncated residuals -/

/-- The truncated real value `min x 1` of an extended nonnegative residual (it tends to zero iff
the residual does, and its smallness controls the residual). -/
def trunc (x : ℝ≥0∞) : ℝ := (min x 1).toReal

theorem min_one_ne_top (x : ℝ≥0∞) : min x 1 ≠ ∞ :=
  ne_top_of_le_ne_top one_ne_top (min_le_right _ _)

theorem trunc_nonneg (x : ℝ≥0∞) : 0 ≤ trunc x := ENNReal.toReal_nonneg

theorem ofReal_trunc (x : ℝ≥0∞) : ENNReal.ofReal (trunc x) = min x 1 :=
  ENNReal.ofReal_toReal (min_one_ne_top x)

theorem trunc_le_trunc {x y : ℝ≥0∞} (h : x ≤ y) : trunc x ≤ trunc y :=
  ENNReal.toReal_mono (min_one_ne_top y) (min_le_min_right _ h)

theorem lt_ofReal_of_trunc_lt {x : ℝ≥0∞} {ε : ℝ} (hε : ε ≤ 1) (h : trunc x < ε) :
    x < ENNReal.ofReal ε := by
  have hε0 : 0 < ε := lt_of_le_of_lt (trunc_nonneg x) h
  have hm : min x 1 < ENNReal.ofReal ε := by
    rw [← ofReal_trunc]; exact (ENNReal.ofReal_lt_ofReal_iff hε0).2 h
  rcases le_total x 1 with hx | hx
  · rwa [min_eq_left hx] at hm
  · rw [min_eq_right hx] at hm
    exact absurd (hm.trans_le (ENNReal.ofReal_le_of_le_toReal (by simpa using hε))) (lt_irrefl _)

theorem le_ofReal_of_trunc_le {x : ℝ≥0∞} {ε : ℝ} (hε : ε < 1) (h : trunc x ≤ ε) :
    x ≤ ENNReal.ofReal ε := by
  have hm : min x 1 ≤ ENNReal.ofReal ε := by
    rw [← ofReal_trunc]; exact ENNReal.ofReal_le_ofReal h
  rcases le_total x 1 with hx | hx
  · rwa [min_eq_left hx] at hm
  · rw [min_eq_right hx] at hm
    have : ENNReal.ofReal ε < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hε
    exact absurd (hm.trans_lt this) (lt_irrefl _)

/-- A small positive real below a positive extended real. -/
theorem exists_real_lt_one_ofReal_le {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ENNReal.ofReal r ≤ ε := by
  by_cases htop : ε = ∞
  · exact ⟨1 / 2, by norm_num, by norm_num, by simp [htop]⟩
  · refine ⟨min ε.toReal (1 / 2), lt_min (ENNReal.toReal_pos hε.ne' htop) (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num), ?_⟩
    calc ENNReal.ofReal (min ε.toReal (1 / 2)) ≤ ENNReal.ofReal ε.toReal :=
          ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = ε := ENNReal.ofReal_toReal htop

theorem tendsto_trunc_iff {f : ℕ → ℝ≥0∞} :
    Tendsto (fun n => trunc (f n)) atTop (𝓝 0) ↔ Tendsto f atTop (𝓝 0) := by
  have key : Tendsto (fun n => trunc (f n)) atTop (𝓝 0) ↔
      Tendsto (fun n => min (f n) 1) atTop (𝓝 0) := by
    have := ENNReal.tendsto_toReal_iff (fi := atTop) (f := fun n => min (f n) 1)
      (fun n => min_one_ne_top (f n)) (x := 0) ENNReal.zero_ne_top
    simpa [trunc] using this
  rw [key]
  constructor
  · intro h
    rw [ENNReal.tendsto_atTop_zero] at h ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h (min ε 2⁻¹) (lt_min hε (by simp))
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rcases le_total (f n) 1 with hx | hx
    · rw [min_eq_left hx] at h1; exact h1.trans (min_le_left _ _)
    · rw [min_eq_right hx] at h1
      exact absurd (h1.trans (min_le_right _ _)) (by norm_num)
  · intro h
    simpa using h.min (tendsto_const_nhds (x := (1 : ℝ≥0∞)))

/-! ### The compact-screen upgrade -/

/-- **Compact-screen upgrade.**  If the masses `‖f_n - S_R f_n‖` outside the declared screens are
uniformly small for large `R` and, for every fixed screen size, the screened records
`S_R f_n` form a Cauchy comparison, then the records themselves form a Cauchy comparison in
`L²(μ)`. -/
theorem cauchy_of_screens {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] {f : ℕ → X → E} {S : ℕ → (X → E) → (X → E)}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hS : ∀ R n, AEStronglyMeasurable (S R (f n)) μ)
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R, ∀ n, eLpNorm (f n - S R (f n)) 2 μ ≤ ε)
    (hcomp : ∀ R, ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      eLpNorm (S R (f m) - S R (f n)) 2 μ < ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, eLpNorm (f m - f n) 2 μ < ε := by
  intro ε hε
  obtain ⟨r, hr0, -, hrε⟩ := exists_real_lt_one_ofReal_le hε
  have h3 : (0 : ℝ≥0∞) < ENNReal.ofReal (r / 3) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨R, hR⟩ := htail _ h3
  obtain ⟨N, hN⟩ := hcomp R _ h3
  refine ⟨N, fun m hm n hn => ?_⟩
  have hsplit : f m - f n = (f m - S R (f m)) + ((S R (f m) - S R (f n)) + (S R (f n) - f n)) := by
    abel
  have hle : eLpNorm (f m - f n) 2 μ ≤ eLpNorm (f m - S R (f m)) 2 μ +
      (eLpNorm (S R (f m) - S R (f n)) 2 μ + eLpNorm (f n - S R (f n)) 2 μ) := by
    rw [hsplit]
    refine (eLpNorm_add_le ((hf m).sub (hS R m)) (((hS R m).sub (hS R n)).add
      ((hS R n).sub (hf n))) (by norm_num)).trans (add_le_add le_rfl ?_)
    refine (eLpNorm_add_le ((hS R m).sub (hS R n)) ((hS R n).sub (hf n)) (by norm_num)).trans ?_
    rw [eLpNorm_sub_comm (S R (f n)) (f n)]
  have htop : ENNReal.ofReal (r / 3) ≠ ∞ := ENNReal.ofReal_ne_top
  calc eLpNorm (f m - f n) 2 μ ≤ _ := hle
    _ < ENNReal.ofReal (r / 3) + (ENNReal.ofReal (r / 3) + ENNReal.ofReal (r / 3)) := by
        refine ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top htop (hR m)) (hR m) ?_
        exact ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top htop (hR n)) (hN m hm n hn)
          (hR n)
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ ε := hrε

/-! ### Completeness of `L²_loc` on an open set -/

/-- A compact exhaustion of an open set of `ℝ^d`. -/
theorem exists_compactExhaustion_opens {d : ℕ} (Ω : Opens (Fin d → ℝ)) :
    ∃ Ck : ℕ → Set (Fin d → ℝ), (∀ k, IsCompact (Ck k)) ∧ (∀ k, Ck k ⊆ Ω) ∧ Monotone Ck ∧
      ∀ C, IsCompact C → C ⊆ Ω → ∃ k, C ⊆ Ck k := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let KX := CompactExhaustion.choice Ω
  refine ⟨fun k => Subtype.val '' KX k, fun k => (KX.isCompact k).image continuous_subtype_val,
    fun k => by rintro _ ⟨x, -, rfl⟩; exact x.2, fun m n h => image_mono (KX.subset h), ?_⟩
  intro C hC hCΩ
  have hC' : IsCompact ((Subtype.val : Ω → Fin d → ℝ) ⁻¹' C) := by
    have himg : (Subtype.val : Ω → Fin d → ℝ) '' (Subtype.val ⁻¹' C) = C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hCΩ hx⟩, hx, rfl⟩
    rw [Subtype.isCompact_iff, himg]
    exact hC
  obtain ⟨k, hk⟩ := KX.exists_superset_of_isCompact hC'
  exact ⟨k, fun x hx => ⟨⟨x, hCΩ hx⟩, hk hx, rfl⟩⟩

/-- Strong `L²_loc` convergence passes to subsequences. -/
theorem l2LocTendsto_comp {E : Type*} [NormedAddCommGroup E] {d : ℕ} {Ω : Opens (Fin d → ℝ)}
    {u : ℕ → Fin d → (Fin d → ℝ) → E} {u' : Fin d → (Fin d → ℝ) → E}
    (h : DistributionalTorsion.L2LocTendsto Ω u u') {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    DistributionalTorsion.L2LocTendsto Ω (fun n => u (φ n)) u' :=
  ⟨fun n => h.memLp (φ n), h.memLp_lim, fun a C hC hCΩ => (h.tendsto a C hC hCΩ).comp
    hφ.tendsto_atTop⟩

/-- **Completeness of `L²_loc(Ω)`.**  A family of `L²_loc` one-forms on an open set `Ω ⊆ ℝ^d`
which is a Cauchy comparison in `L²(C)` on every compact `C ⊆ Ω` converges strongly in
`L²_loc(Ω)`, and a subsequence (diagonal on a compact exhaustion) converges almost everywhere
on `Ω`. -/
theorem exists_l2LocTendsto_of_cauchy {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {d : ℕ} (Ω : Opens (Fin d → ℝ)) (u : ℕ → Fin d → (Fin d → ℝ) → E)
    (hu : ∀ n a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (u n a) 2 (volume.restrict C))
    (hcau : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N, ∀ m ≥ N, ∀ n ≥ N, eLpNorm (u m a - u n a) 2 (volume.restrict C) < ε) :
    ∃ u' : Fin d → (Fin d → ℝ) → E, DistributionalTorsion.L2LocTendsto Ω u u' ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ x, x ∈ Ω → ∀ a, Tendsto (fun j => u (φ j) a x) atTop (𝓝 (u' a x)) := by
  obtain ⟨Ck, hCk, hCkΩ, hmono, hcov⟩ := exists_compactExhaustion_opens Ω
  have hjoint : ∀ k, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ a,
      eLpNorm (u m a - u n a) 2 (volume.restrict (Ck k)) < (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have hpos : (0 : ℝ≥0∞) < 2⁻¹ ^ k := ENNReal.pow_pos (by simp) k
    choose N hN using fun a => hcau a (Ck k) (hCk k) (hCkΩ k) _ hpos
    exact ⟨Finset.univ.sup N, fun m hm n hn a =>
      hN a m (le_trans (Finset.le_sup (Finset.mem_univ a)) hm) n
        (le_trans (Finset.le_sup (Finset.mem_univ a)) hn)⟩
  choose N hN using hjoint
  set φ : ℕ → ℕ := fun k => (∑ i ∈ Finset.range (k + 1), N i) + k with hφdef
  have hφmono : StrictMono φ := strictMono_nat_of_lt_succ fun k => by
    simp only [hφdef, Finset.sum_range_succ]; omega
  have hφN : ∀ k, N k ≤ φ k := fun k => by
    simp only [hφdef, Finset.sum_range_succ]; omega
  have hsmall : ∀ j k, j ≤ k → ∀ m ≥ φ k, ∀ n ≥ φ k, ∀ a,
      eLpNorm (u m a - u n a) 2 (volume.restrict (Ck j)) < (2⁻¹ : ℝ≥0∞) ^ k := by
    intro j k hjk m hm n hn a
    exact lt_of_le_of_lt (eLpNorm_mono_measure _ (Measure.restrict_mono (hmono hjk) le_rfl))
      (hN k m ((hφN k).trans hm) n ((hφN k).trans hn) a)
  have hB : ∑' i, (2⁻¹ : ℝ≥0∞) ^ i ≠ ∞ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hae : ∀ j a, ∀ᵐ x ∂(volume.restrict (Ck j)),
      ∃ l, Tendsto (fun i => u (φ i) a x) atTop (𝓝 l) := by
    intro j a
    have h := Lp.ae_tendsto_of_cauchy_eLpNorm (μ := volume.restrict (Ck j)) (p := 2)
      (f := fun i => u (φ (i + j)) a) (fun i => (hu _ a _ (hCk j) (hCkΩ j)).1) (by norm_num) hB
      (fun M n m hn hm => by
        have h1 := hsmall j (M + j) (by omega) (φ (n + j)) (hφmono.monotone (by omega))
          (φ (m + j)) (hφmono.monotone (by omega)) a
        refine h1.trans_le ?_
        exact pow_le_pow_of_le_one (zero_le) (ENNReal.inv_le_one.2 one_le_two)
          (by omega))
    filter_upwards [h] with x ⟨l, hl⟩
    exact ⟨l, (tendsto_add_atTop_iff_nat j).1 hl⟩
  let u' : Fin d → (Fin d → ℝ) → E := fun a x => limUnder atTop (fun i => u (φ i) a x)
  have hconv : ∀ᵐ x, x ∈ Ω → ∀ a, Tendsto (fun i => u (φ i) a x) atTop (𝓝 (u' a x)) := by
    have hconvj : ∀ j, ∀ᵐ x, x ∈ Ck j → ∀ a,
        Tendsto (fun i => u (φ i) a x) atTop (𝓝 (u' a x)) := by
      intro j
      have h := ae_all_iff.2 (hae j)
      rw [ae_restrict_iff' (hCk j).measurableSet] at h
      filter_upwards [h] with x hx hxj a
      exact tendsto_nhds_limUnder (hx hxj a)
    filter_upwards [ae_all_iff.2 hconvj] with x hx hxΩ a
    obtain ⟨j, hj⟩ := hcov {x} isCompact_singleton (singleton_subset_iff.2 hxΩ)
    exact hx j (hj rfl) a
  have hconvC : ∀ C : Set (Fin d → ℝ), IsCompact C → C ⊆ Ω → ∀ᵐ x ∂(volume.restrict C),
      ∀ a, Tendsto (fun i => u (φ i) a x) atTop (𝓝 (u' a x)) := fun C hC hCΩ =>
    (ae_restrict_iff' hC.measurableSet).2 (hconv.mono fun x hx hxC => hx (hCΩ hxC))
  have htend : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      Tendsto (fun n => eLpNorm (u n a - u' a) 2 (volume.restrict C)) atTop (𝓝 0) := by
    intro a C hC hCΩ
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    obtain ⟨M, hM⟩ := hcau a C hC hCΩ ε hε
    refine ⟨M, fun n hn => ?_⟩
    have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) (μ := volume.restrict C)
      (f := fun i => u n a - u (φ i) a)
      (fun i => ((hu n a C hC hCΩ).sub (hu (φ i) a C hC hCΩ)).1) (u n a - u' a)
      ((hconvC C hC hCΩ).mono fun x hx => tendsto_const_nhds.sub (hx a))
    refine hlim.trans (liminf_le_of_frequently_le' ?_)
    refine (eventually_atTop.2 ⟨M, fun i hi => ?_⟩).frequently
    exact (hM n hn (φ i) (hi.trans (hφmono.id_le i))).le
  have hmemLim : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (u' a) 2 (volume.restrict C) := by
    intro a C hC hCΩ
    have hmeas : AEStronglyMeasurable (u' a) (volume.restrict C) :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun i => (hu (φ i) a C hC hCΩ).1)
        ((hconvC C hC hCΩ).mono fun x hx => hx a)
    obtain ⟨n, hn⟩ := ((htend a C hC hCΩ).eventually (gt_mem_nhds one_pos)).exists
    have hd : MemLp (u n a - u' a) 2 (volume.restrict C) :=
      ⟨(hu n a C hC hCΩ).1.sub hmeas, hn.trans ENNReal.one_lt_top⟩
    simpa using (hu n a C hC hCΩ).sub hd
  exact ⟨u', ⟨hu, hmemLim, htend⟩, φ, hφmono, hconv⟩

/-! ### Curvature propagation records and their budgets -/

section Propagation

open scoped InnerProductSpace

/-- **Continuous curvature propagation record** (`eq:main-curvature-propagation-writer`,
`eq:main-curvature-incidence`) of one finite record on a compact foliated cylinder with time
interval `[0, T]`: the retained electric/magnetic coefficients `y` in a finite-dimensional inner
product space `V` (whose dimension may depend on the cutoff), the positive physical Gram `M`, the
`M`-skew principal block `K`, the lower-order block `L`, the complete differentiated source `f`,
the growth rate `a` (`eq:main-curvature-growth`), the slice norms `ρ t = ‖𝓘 y(t)‖_{L²(Σ_t)}` of the
stable interpolation, the lapse `N` with its bound, the interpolation constant `C_I` and the
reconstruction-error constant `C_ζ`.  The family `q` lists the curvature sizes to be controlled
(the `L²` norms of the curvature components on the compact), each bounded through the slice
decomposition `R = 𝓘 y + ζ`. -/
structure ContinuousPropagationRecord (T : ℝ) {κ : Type*} (q : κ → ℝ) where
  V : Type
  [normedAddCommGroup : NormedAddCommGroup V]
  [innerProductSpace : InnerProductSpace ℝ V]
  M : ℝ → V →L[ℝ] V
  M' : ℝ → V →L[ℝ] V
  K : ℝ → V →L[ℝ] V
  L : ℝ → V →L[ℝ] V
  y : ℝ → V
  y' : ℝ → V
  f : ℝ → V
  a : ℝ → ℝ
  hasDerivAt_M : ∀ t, HasDerivAt M (M' t) t
  hasDerivAt_y : ∀ t, HasDerivAt y (y' t) t
  continuous_f : Continuous f
  continuous_a : Continuous a
  a_nonneg : ∀ t, 0 ≤ a t
  gram_symm : ∀ t x z, ⟪M t x, z⟫_ℝ = ⟪x, M t z⟫_ℝ
  gram_nonneg : ∀ t x, 0 ≤ ⟪x, M t x⟫_ℝ
  /-- The writer form `ẏ = (K + L) y + f`. -/
  writer : ∀ t, y' t = (K t + L t) (y t) + f t
  /-- The principal block is `M`-skew (`M K + Kᵀ M = 0`). -/
  skew : ∀ t x, ⟪M t x, K t x⟫_ℝ = 0
  /-- The growth rate dominates the symmetric part (`eq:main-curvature-growth`). -/
  growth : ∀ t x, ⟪x, M' t x⟫_ℝ + 2 * ⟪M t x, L t x⟫_ℝ ≤ 2 * a t * ⟪x, M t x⟫_ℝ
  ρ : ℝ → ℝ
  N : ℝ → ℝ
  lapseBound : ℝ
  CI : ℝ
  Cζ : ℝ
  CI_nonneg : 0 ≤ CI
  /-- Stable interpolation `‖𝓘 y(t)‖_{L²(Σ_t)} ≤ C_I z(t)`. -/
  incidence : ∀ t ∈ Set.Icc 0 T, 0 ≤ ρ t ∧ ρ t ≤ CI * gramEnergy M y t
  /-- Lapse bound `0 ≤ N ≤ N_*`. -/
  lapse : ∀ t ∈ Set.Icc 0 T, 0 ≤ N t ∧ N t ≤ lapseBound
  integrable : IntervalIntegrable (fun t => N t * ρ t ^ 2) volume 0 T
  /-- The slice decomposition `R = 𝓘 y + ζ`, `‖ζ‖_{L²} ≤ C_ζ`, of every controlled curvature
  size. -/
  slice : ∀ i, q i ≤ Real.sqrt (∫ t in (0 : ℝ)..T, N t * ρ t ^ 2) + Cζ

attribute [instance] ContinuousPropagationRecord.normedAddCommGroup
  ContinuousPropagationRecord.innerProductSpace

namespace ContinuousPropagationRecord

variable {T : ℝ} {κ : Type*} {q : κ → ℝ}

/-- Initial energy budget `z(0)`. -/
def initialBudget (P : ContinuousPropagationRecord T q) : ℝ := gramEnergy P.M P.y 0

/-- Growth budget `∫₀ᵀ a`. -/
def growthBudget (P : ContinuousPropagationRecord T q) : ℝ := ∫ t in (0 : ℝ)..T, P.a t

/-- Differentiated-source budget `∫₀ᵀ ‖f‖_M` (it contains the transferred Palatini row). -/
def sourceBudget (P : ContinuousPropagationRecord T q) : ℝ :=
  ∫ t in (0 : ℝ)..T, gramEnergy P.M P.f t

theorem initialBudget_nonneg (P : ContinuousPropagationRecord T q) : 0 ≤ P.initialBudget :=
  Real.sqrt_nonneg _

theorem sourceBudget_nonneg (hT : 0 ≤ T) (P : ContinuousPropagationRecord T q) :
    0 ≤ P.sourceBudget :=
  intervalIntegral.integral_nonneg hT fun _ _ => Real.sqrt_nonneg _

/-- `thm:main-curvature-propagation` on one record: the curvature sizes are bounded by
`C_I √(N_* T) e^{A}(Z + F) + C_ζ` for any upper bounds of the budgets. -/
theorem le_of_budgets (hT : 0 ≤ T) (P : ContinuousPropagationRecord T q) {Z A F : ℝ}
    (hZ : P.initialBudget ≤ Z) (hA : P.growthBudget ≤ A) (hF : P.sourceBudget ≤ F) (i : κ) :
    q i ≤ P.CI * Real.sqrt (P.lapseBound * T) * (Real.exp A * (Z + F)) + P.Cζ := by
  have hz := curvature_energy_uniform_bound P.M P.M' P.K P.L P.y P.y' P.f P.a P.hasDerivAt_M
    P.hasDerivAt_y P.continuous_f P.continuous_a P.a_nonneg P.gram_symm P.gram_nonneg P.writer
    P.skew P.growth hT hZ hA hF
  have hB : 0 ≤ Real.exp A * (Z + F) :=
    mul_nonneg (Real.exp_pos A).le (add_nonneg (P.initialBudget_nonneg.trans hZ)
      ((P.sourceBudget_nonneg hT).trans hF))
  exact derived_l2_curvature_bound (gramEnergy P.M P.y) P.ρ P.N hT P.CI_nonneg hB hz
    (fun t _ => Real.sqrt_nonneg _) P.incidence P.lapse P.integrable (P.slice i)

end ContinuousPropagationRecord

/-- **Fully discrete curvature propagation record** (`eq:main-discrete-curvature-update`) of one
finite record: steps `s_j`, growth rates `a_j`, transfer exponents `d_j`
(`‖T_j‖ ≤ e^{d_j}`), skew principal blocks `K_j`, lower-order blocks `L_j`, the actual records
`Y_j` and complete step residuals `ε_j`, the step bound `b < 1`, and the stable interval
interpolation with constant `C_I` (including the lapse and time factors) and reconstruction
error `C_ζ`. -/
structure DiscretePropagationRecord {κ : Type*} (q : κ → ℝ) where
  V : Type
  [normedAddCommGroup : NormedAddCommGroup V]
  [innerProductSpace : InnerProductSpace ℝ V]
  [finiteDimensional : FiniteDimensional ℝ V]
  steps : ℕ
  s : ℕ → ℝ
  a : ℕ → ℝ
  d : ℕ → ℝ
  K : ℕ → V →L[ℝ] V
  L : ℕ → V →L[ℝ] V
  Tr : ℕ → V →L[ℝ] V
  Y : ℕ → V
  ε : ℕ → V
  b : ℝ
  b_lt_one : b < 1
  s_pos : ∀ j < steps, 0 < s j
  a_nonneg : ∀ j < steps, 0 ≤ a j
  d_nonneg : ∀ j < steps, 0 ≤ d j
  skew : ∀ j < steps, ∀ x z, ⟪K j x, z⟫_ℝ = -⟪x, K j z⟫_ℝ
  growth : ∀ j < steps, ∀ x, ⟪x, L j x⟫_ℝ ≤ a j * ‖x‖ ^ 2
  transfer : ∀ j < steps, ‖Tr j‖ ≤ Real.exp (d j)
  step_bound : ∀ j < steps, s j * a j / 2 ≤ b
  update : ∀ j < steps, Y (j + 1) - Tr j (Y j) =
    s j • (K j + L j) ((1 / 2 : ℝ) • (Y (j + 1) + Tr j (Y j))) + ε j
  CI : ℝ
  Cζ : ℝ
  CI_nonneg : 0 ≤ CI
  /-- Stable interval interpolation: a uniform bound on the recorded steps bounds every
  controlled curvature size. -/
  slice : ∀ B, (∀ j ≤ steps, ‖Y j‖ ≤ B) → ∀ i, q i ≤ CI * B + Cζ

attribute [instance] DiscretePropagationRecord.normedAddCommGroup
  DiscretePropagationRecord.innerProductSpace DiscretePropagationRecord.finiteDimensional

namespace DiscretePropagationRecord

variable {κ : Type*} {q : κ → ℝ}

/-- Transfer budget `D = Σ d_j`. -/
def transferBudget (P : DiscretePropagationRecord q) : ℝ := ∑ j ∈ Finset.range P.steps, P.d j

/-- Growth budget `A^d = Σ s_j a_j`. -/
def growthBudget (P : DiscretePropagationRecord q) : ℝ :=
  ∑ j ∈ Finset.range P.steps, P.s j * P.a j

/-- Source budget `𝒟 = Σ ‖ε_j‖²/s_j`. -/
def sourceBudget (P : DiscretePropagationRecord q) : ℝ :=
  ∑ j ∈ Finset.range P.steps, ‖P.ε j‖ ^ 2 / P.s j

/-- Duration `T = Σ s_j`. -/
def durationBudget (P : DiscretePropagationRecord q) : ℝ := ∑ j ∈ Finset.range P.steps, P.s j

/-- Initial energy `‖Y_0‖`. -/
def initialBudget (P : DiscretePropagationRecord q) : ℝ := ‖P.Y 0‖

theorem growthBudget_nonneg (P : DiscretePropagationRecord q) : 0 ≤ P.growthBudget :=
  Finset.sum_nonneg fun j hj =>
    mul_nonneg (P.s_pos j (Finset.mem_range.1 hj)).le (P.a_nonneg j (Finset.mem_range.1 hj))

theorem sourceBudget_nonneg (P : DiscretePropagationRecord q) : 0 ≤ P.sourceBudget :=
  Finset.sum_nonneg fun j hj => div_nonneg (sq_nonneg _) (P.s_pos j (Finset.mem_range.1 hj)).le

theorem durationBudget_nonneg (P : DiscretePropagationRecord q) : 0 ≤ P.durationBudget :=
  Finset.sum_nonneg fun j hj => (P.s_pos j (Finset.mem_range.1 hj)).le

/-- `thm:main-discrete-curvature` on one record, with upper bounds of the budgets and a lower
bound `c ≤ 1 - b` of the step margin. -/
theorem le_of_budgets (P : DiscretePropagationRecord q) {D A S Tm Y0 c : ℝ} (hc : 0 < c)
    (hD : P.transferBudget ≤ D) (hA : P.growthBudget ≤ A) (hS : P.sourceBudget ≤ S)
    (hT : P.durationBudget ≤ Tm) (hY : P.initialBudget ≤ Y0) (hb : c ≤ 1 - P.b) (i : κ) :
    q i ≤ P.CI * (Real.exp (D + A / c) * (Y0 + Real.sqrt (Tm * S) / c)) + P.Cζ := by
  obtain ⟨-, hbound⟩ := discrete_curvature_certificate P.steps P.s P.a P.d P.K P.L P.Tr P.Y P.ε
    P.b P.b_lt_one P.s_pos P.a_nonneg P.d_nonneg P.skew P.growth P.transfer P.step_bound P.update
  have h1b : 0 < 1 - P.b := by linarith [P.b_lt_one]
  have hA0 := P.growthBudget_nonneg
  have hS0 := P.sourceBudget_nonneg
  have hT0 := P.durationBudget_nonneg
  refine P.slice _ (fun j hj => (hbound j hj).trans ?_) i
  have hexp : Real.exp (∑ i ∈ Finset.range P.steps, P.d i +
      (∑ i ∈ Finset.range P.steps, P.s i * P.a i) / (1 - P.b)) ≤ Real.exp (D + A / c) := by
    apply Real.exp_le_exp.2
    refine add_le_add hD ?_
    calc (∑ i ∈ Finset.range P.steps, P.s i * P.a i) / (1 - P.b) ≤ A / (1 - P.b) :=
          div_le_div_of_nonneg_right hA h1b.le
      _ ≤ A / c := div_le_div_of_nonneg_left (hA0.trans hA) hc hb
  have hsq : Real.sqrt ((∑ i ∈ Finset.range P.steps, P.s i) *
      ∑ i ∈ Finset.range P.steps, ‖P.ε i‖ ^ 2 / P.s i) ≤ Real.sqrt (Tm * S) :=
    Real.sqrt_le_sqrt (mul_le_mul hT hS hS0 (hT0.trans hT))
  have hinner : ‖P.Y 0‖ + Real.sqrt ((∑ i ∈ Finset.range P.steps, P.s i) *
      ∑ i ∈ Finset.range P.steps, ‖P.ε i‖ ^ 2 / P.s i) / (1 - P.b) ≤
      Y0 + Real.sqrt (Tm * S) / c := by
    refine add_le_add hY ?_
    calc _ ≤ Real.sqrt (Tm * S) / (1 - P.b) := div_le_div_of_nonneg_right hsq h1b.le
      _ ≤ Real.sqrt (Tm * S) / c := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hc hb
  exact mul_le_mul hexp hinner (by positivity) (Real.exp_pos _).le

end DiscretePropagationRecord

end Propagation

/-- A uniform bound on a tail and individual bounds on the finitely many earlier records give a
uniform bound. -/
theorem exists_forall_le_of_eventually {κ : Type*} {q : ℕ → κ → ℝ}
    (hind : ∀ n, ∃ B, ∀ i, q n i ≤ B) (htail : ∃ N B, ∀ n ≥ N, ∀ i, q n i ≤ B) :
    ∃ B, ∀ n i, q n i ≤ B := by
  obtain ⟨N, B, hB⟩ := htail
  choose b hb using hind
  refine ⟨max B (∑ n ∈ Finset.range N, |b n|), fun n i => ?_⟩
  by_cases hn : N ≤ n
  · exact (hB n hn i).trans (le_max_left _ _)
  · refine (hb n i).trans ((le_abs_self _).trans (le_trans ?_ (le_max_right _ _)))
    exact Finset.single_le_sum (f := fun n => |b n|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (not_le.1 hn))

/-! ### Elementary conversions of passing certificates -/

/-- A passing calibrated comparison `|u_m - u_n|` gives a limit. -/
theorem exists_tendsto_of_comparison_passes {u : ℕ → ℝ}
    (h : (Certificate.comparison fun m n => |u m - u n|).Passes) :
    ∃ l, Tendsto u atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun m hm n hn => by rw [Real.dist_eq]; exact hN m hm n hn⟩)

/-- A passing margin `|u_n| ≥ c > 0` keeps the limit away from zero. -/
theorem ne_zero_of_margin_passes {u : ℕ → ℝ} {l : ℝ}
    (h : (Certificate.margin fun n => |u n|).Passes) (hl : Tendsto u atTop (𝓝 l)) : l ≠ 0 := by
  obtain ⟨c, hc, hev⟩ := h
  have : c ≤ |l| := ge_of_tendsto hl.abs hev
  intro h0
  rw [h0, abs_zero] at this
  linarith

/-- A passing budget of finite extended norms gives a uniform finite bound. -/
theorem exists_bound_of_budget_passes {x : ℕ → ℝ≥0∞} (hfin : ∀ n, x n ≠ ∞)
    (h : (Certificate.budget fun n => (x n).toReal).Passes) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, x n ≤ M := by
  obtain ⟨B, hB⟩ := h
  refine ⟨ENNReal.ofReal B, ENNReal.ofReal_ne_top, fun n => ?_⟩
  rw [← ENNReal.ofReal_toReal (hfin n)]
  exact ENNReal.ofReal_le_ofReal (hB ⟨n, rfl⟩)

/-- The capped margin `sup {κ ∈ [0,1] | P κ}` of a downward closed property. -/
def cappedMargin (P : ℝ → Prop) : ℝ := sSup {κ | κ ∈ Set.Icc (0 : ℝ) 1 ∧ P κ}

/-- A positive lower bound `c` on a capped margin certifies the property at `c/2`. -/
theorem of_le_cappedMargin {P : ℝ → Prop} (hP : ∀ κ κ', P κ' → κ ≤ κ' → P κ) {c : ℝ}
    (hc : 0 < c) (h : c ≤ cappedMargin P) : P (c / 2) := by
  set S := {κ | κ ∈ Set.Icc (0 : ℝ) 1 ∧ P κ}
  have hbdd : BddAbove S := ⟨1, fun κ hκ => hκ.1.2⟩
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : cappedMargin P = 0 := by
      show sSup S = 0
      rw [hne, Real.sSup_empty]
    linarith
  obtain ⟨κ, hκ, hlt⟩ := exists_lt_of_lt_csSup hne (show c / 2 < sSup S by
    have : c ≤ sSup S := h
    linarith)
  exact hP _ _ hκ.2 hlt.le

/-- A certified value in `[0,1]` bounds the capped margin from below. -/
theorem le_cappedMargin {P : ℝ → Prop} {κ : ℝ} (hκ : κ ∈ Set.Icc (0 : ℝ) 1) (hP : P κ) :
    κ ≤ cappedMargin P :=
  le_csSup ⟨1, fun _ h => h.1.2⟩ ⟨hκ, hP⟩

/-- An essential-supremum residual tending to zero gives almost-everywhere convergence. -/
theorem ae_tendsto_zero_of_eLpNorm_top {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] {f : ℕ → X → E}
    (h : Tendsto (fun n => eLpNorm (f n) ∞ μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0) := by
  filter_upwards [ae_all_iff.2 fun n => ae_le_eLpNormEssSup (μ := μ) (f := f n)] with x hx
  have h1 : Tendsto (fun n => ‖f n x‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
      fun n => by simpa [eLpNorm_exponent_top] using hx n
  have h2 : Tendsto (fun n => ‖f n x‖) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using this
  exact tendsto_zero_iff_norm_tendsto_zero.2 h2

/-- A finite essential supremum bounds the function almost everywhere. -/
theorem ae_norm_le_of_eLpNorm_top_le {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] {f : X → E} {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f ∞ μ ≤ ENNReal.ofReal B) : ∀ᵐ x ∂μ, ‖f x‖ ≤ B := by
  filter_upwards [ae_le_eLpNormEssSup (μ := μ) (f := f)] with x hx
  have h1 : ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal B := by
    rw [ofReal_norm]
    exact hx.trans (by simpa [eLpNorm_exponent_top] using h)
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h1

/-! ### Declared screens, endpoint cut records, connection routes -/

/-- **Declared screens** for a sequence of fields `f n` in `L²(μ)` (the transported finite-rank
spectral screens of `thm:main-spatial-screen` on the common cylinder, including temporal control;
typed data — the manuscript describes the transport in words): screen maps `S_R`, measurable on the
records, exhausting each record (`‖f_n - S_R f_n‖ → 0` as `R → ∞`) and nested (antitone tails). -/
structure ScreenFamily {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X)
    (f : ℕ → X → E) where
  screen : ℕ → (X → E) → (X → E)
  aestronglyMeasurable : ∀ R n, AEStronglyMeasurable (screen R (f n)) μ
  exhausting : ∀ n, Tendsto (fun R => eLpNorm (f n - screen R (f n)) 2 μ) atTop (𝓝 0)
  nested : ∀ n, Antitone fun R => eLpNorm (f n - screen R (f n)) 2 μ

namespace ScreenFamily

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
  {f : ℕ → X → E}

/-- The common-cylinder compactness tail: (truncated) mass of record `n` outside screen `R`. -/
def tailCert (S : ScreenFamily μ f) : Certificate :=
  .tail fun n R => trunc (eLpNorm (f n - S.screen R (f n)) 2 μ)

/-- The transported-screen calibrated comparison at screen size `R`. -/
def comparisonCert (S : ScreenFamily μ f) (R : ℕ) : Certificate :=
  .comparison fun m n => trunc (eLpNorm (S.screen R (f m) - S.screen R (f n)) 2 μ)

theorem tailCert_admissible (S : ScreenFamily μ f) : S.tailCert.Admissible :=
  ⟨fun n => tendsto_trunc_iff.2 (S.exhausting n), fun n _ _ h => trunc_le_trunc (S.nested n h)⟩

/-- Passing tail and transported-screen comparisons give a Cauchy comparison of the records
(compact-screen upgrade). -/
theorem cauchy (S : ScreenFamily μ f) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (ht : S.tailCert.Passes) (hc : ∀ R, (S.comparisonCert R).Passes) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, eLpNorm (f m - f n) 2 μ < ε :=
  cauchy_of_screens hf S.aestronglyMeasurable
    (fun ε hε => by
      obtain ⟨r, hr0, hr1, hrε⟩ := exists_real_lt_one_ofReal_le hε
      obtain ⟨R, hR⟩ := ht r hr0
      exact ⟨R, fun n => (le_ofReal_of_trunc_le hr1 (hR n)).trans hrε⟩)
    (fun R ε hε => by
      obtain ⟨r, hr0, hr1, hrε⟩ := exists_real_lt_one_ofReal_le hε
      obtain ⟨N, hN⟩ := hc R r hr0
      exact ⟨N, fun m hm n hn => (lt_ofReal_of_trunc_lt hr1.le (hN m hm n hn)).trans_le hrε⟩)

/-- The identity screens of a sequence of measurable fields. -/
def identity (f : ℕ → X → E) (hf : ∀ n, AEStronglyMeasurable (f n) μ) : ScreenFamily μ f where
  screen _ g := g
  aestronglyMeasurable _ n := hf n
  exhausting _ := by simp
  nested _ _ _ _ := by simp

end ScreenFamily

/-- The **endpoint cut record** of one finite record (`thm:main-spatial-screen`): a finite
weighted graph with its efficient capacities; its margin is the efficient cut constant
`I^eff`. -/
structure EndpointCutRecord where
  V : Type
  [fintype : Fintype V]
  [nonempty : Nonempty V]
  [decEq : DecidableEq V]
  graph : FiniteWeightedGraph V
  capacity : V → V → ℝ

attribute [instance] EndpointCutRecord.fintype EndpointCutRecord.nonempty EndpointCutRecord.decEq

/-- The efficient cut constant `I^eff_X` of an endpoint cut record. -/
def EndpointCutRecord.margin (c : EndpointCutRecord) : ℝ :=
  c.graph.efficientCutConstant c.capacity

/-- The items of a curvature propagation certificate: initial, growth, transfer,
differentiated-source and duration budgets, lapse bound, interpolation stability,
reconstruction error and step margin. -/
inductive CurvatureItem
  | initial | growth | transfer | source | duration | lapse | stability | reconstruction
  | stepMargin

/-- The curvature propagation route on one compact: the continuous certificate
`thm:main-curvature-propagation` or the fully discrete certificate `thm:main-discrete-curvature`,
for every finite record. -/
inductive CurvatureRoute (q : ℕ → Fin 4 × Fin 4 → ℝ) : Type 1
  | continuous (T : ℝ) (hT : 0 ≤ T) (P : ∀ n, ContinuousPropagationRecord T (q n))
  | discrete (P : ∀ n, DiscretePropagationRecord (q n))

namespace CurvatureRoute

variable {q : ℕ → Fin 4 × Fin 4 → ℝ}

/-- The certificates of a curvature route (items that do not occur on the route pass
trivially: on the continuous route the transfer is part of the source and the time interval is
fixed; on the discrete route the lapse is part of the interpolation constant). -/
def cert : CurvatureRoute q → CurvatureItem → Certificate
  | continuous _ _ P, .initial => .budget fun n => (P n).initialBudget
  | continuous _ _ P, .growth => .budget fun n => (P n).growthBudget
  | continuous _ _ P, .source => .budget fun n => (P n).sourceBudget
  | continuous _ _ P, .lapse => .budget fun n => (P n).lapseBound
  | continuous _ _ P, .stability => .budget fun n => (P n).CI
  | continuous _ _ P, .reconstruction => .budget fun n => (P n).Cζ
  | continuous _ _ _, .transfer => Certificate.trivial
  | continuous _ _ _, .duration => Certificate.trivial
  | continuous _ _ _, .stepMargin => Certificate.trivial
  | discrete P, .initial => .budget fun n => (P n).initialBudget
  | discrete P, .growth => .budget fun n => (P n).growthBudget
  | discrete P, .transfer => .budget fun n => (P n).transferBudget
  | discrete P, .source => .budget fun n => (P n).sourceBudget
  | discrete P, .duration => .budget fun n => (P n).durationBudget
  | discrete P, .stability => .budget fun n => (P n).CI
  | discrete P, .reconstruction => .budget fun n => (P n).Cζ
  | discrete P, .stepMargin => .margin fun n => 1 - (P n).b
  | discrete _, .lapse => Certificate.trivial

theorem cert_admissible (r : CurvatureRoute q) (i : CurvatureItem) : (r.cert i).Admissible := by
  cases r <;> cases i <;> exact True.intro

/-- **Passing propagation certificates bound the curvature records uniformly.** -/
theorem bounded (r : CurvatureRoute q) (h : ∀ i, (r.cert i).Passes) :
    ∃ B, ∀ n i, q n i ≤ B := by
  cases r with
  | continuous T hT P =>
    obtain ⟨Z, hZ⟩ : BddAbove (Set.range fun n => (P n).initialBudget) := h .initial
    obtain ⟨A, hA⟩ : BddAbove (Set.range fun n => (P n).growthBudget) := h .growth
    obtain ⟨F, hF⟩ : BddAbove (Set.range fun n => (P n).sourceBudget) := h .source
    obtain ⟨Lb, hL⟩ : BddAbove (Set.range fun n => (P n).lapseBound) := h .lapse
    obtain ⟨CI, hCI⟩ : BddAbove (Set.range fun n => (P n).CI) := h .stability
    obtain ⟨Cz, hCz⟩ : BddAbove (Set.range fun n => (P n).Cζ) := h .reconstruction
    have hZ0 : 0 ≤ Z := (P 0).initialBudget_nonneg.trans (hZ ⟨0, rfl⟩)
    have hF0 : 0 ≤ F := ((P 0).sourceBudget_nonneg hT).trans (hF ⟨0, rfl⟩)
    have hCI0 : 0 ≤ CI := (P 0).CI_nonneg.trans (hCI ⟨0, rfl⟩)
    have hB0 : 0 ≤ Real.exp A * (Z + F) := by positivity
    refine ⟨CI * Real.sqrt (Lb * T) * (Real.exp A * (Z + F)) + Cz, fun n i => ?_⟩
    refine ((P n).le_of_budgets hT (hZ ⟨n, rfl⟩) (hA ⟨n, rfl⟩) (hF ⟨n, rfl⟩) i).trans ?_
    refine add_le_add (mul_le_mul_of_nonneg_right ?_ hB0) (hCz ⟨n, rfl⟩)
    exact mul_le_mul (hCI ⟨n, rfl⟩)
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hL ⟨n, rfl⟩) hT)) (Real.sqrt_nonneg _) hCI0
  | discrete P =>
    obtain ⟨D, hD⟩ : BddAbove (Set.range fun n => (P n).transferBudget) := h .transfer
    obtain ⟨A, hA⟩ : BddAbove (Set.range fun n => (P n).growthBudget) := h .growth
    obtain ⟨S, hS⟩ : BddAbove (Set.range fun n => (P n).sourceBudget) := h .source
    obtain ⟨Tm, hT⟩ : BddAbove (Set.range fun n => (P n).durationBudget) := h .duration
    obtain ⟨Y0, hY⟩ : BddAbove (Set.range fun n => (P n).initialBudget) := h .initial
    obtain ⟨CI, hCI⟩ : BddAbove (Set.range fun n => (P n).CI) := h .stability
    obtain ⟨Cz, hCz⟩ : BddAbove (Set.range fun n => (P n).Cζ) := h .reconstruction
    obtain ⟨c, hc, hev⟩ : ∃ c > 0, ∀ᶠ n in atTop, c ≤ 1 - (P n).b := h .stepMargin
    have hCI0 : 0 ≤ CI := (P 0).CI_nonneg.trans (hCI ⟨0, rfl⟩)
    have hY0 : 0 ≤ Y0 := (norm_nonneg _).trans (hY ⟨0, rfl⟩)
    refine exists_forall_le_of_eventually (fun n => ?_) ?_
    · have h1b : 0 < 1 - (P n).b := by linarith [(P n).b_lt_one]
      exact ⟨_, (P n).le_of_budgets h1b le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl⟩
    · obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      have hB0 : 0 ≤ Real.exp (D + A / c) * (Y0 + Real.sqrt (Tm * S) / c) := by positivity
      refine ⟨N, CI * (Real.exp (D + A / c) * (Y0 + Real.sqrt (Tm * S) / c)) + Cz,
        fun n hn i => ?_⟩
      refine ((P n).le_of_budgets hc (hD ⟨n, rfl⟩) (hA ⟨n, rfl⟩) (hS ⟨n, rfl⟩) (hT ⟨n, rfl⟩)
        (hY ⟨n, rfl⟩) (hN n hn) i).trans ?_
      exact add_le_add (mul_le_mul_of_nonneg_right (hCI ⟨n, rfl⟩) hB0) (hCz ⟨n, rfl⟩)

end CurvatureRoute

/-! ### The certification procedure `(E1)`–`(E5)` on the finite records -/

section Procedure

open DistributionalTorsion DistributionalCurvature LimitEinsteinInsertion PalatiniEinsteinAlgebra
  RenewalPalatiniHandoff RenewalEinstein

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Compact subsets of an open cylinder (the index of the local certificates). -/
abbrev CompactIn (Ω : Opens (Fin 4 → ℝ)) := {C : Set (Fin 4 → ℝ) // IsCompact C ∧ C ⊆ Ω}

/-- The periodic literal-link route of `(E5)` (`thm:main-literal-link-compactness`): the
dimensionless identity-chart defect `h max|A_{i,h}| - δ_*` (`eq:main-link-chart`) and the
anisotropic energy of `eq:main-link-energy`, computed on the periodic link records (typed data),
together with the output of the literal-link compactness theorem transported to the common
cylinder: when the chart holds on a cofinal tail and the energy stays bounded, a subsequence
satisfies the literal-link certificate of `(E5)`. -/
structure LiteralLinkRoute (Ω : Opens (Fin 4 → ℝ))
    (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (t : Fin 4) where
  chartDefect : ℕ → ℝ
  energy : ℕ → ℝ
  compactness : (∀ᶠ n in atTop, chartDefect n ≤ 0) → BddAbove (Set.range energy) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ωL RL,
      LiteralLinkCertificate Ω (fun n => ω (φ n)) (fun n => R (φ n)) ωL RL t

/-- Items of the literal-link chart/energy criterion. -/
inductive LiteralItem
  | chart | energy

/-- The literal-link chart/energy certificates. -/
def LiteralLinkRoute.cert {Ω : Opens (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4}
    (L : LiteralLinkRoute Ω ω R t) : LiteralItem → Certificate
  | .chart => .algebraic fun n => L.chartDefect n ≤ 0
  | .energy => .budget L.energy

/-- The inverse-metric test lift `-½ k g` at the regulator coframe (the limit target of the
physical lift coefficient tensors). -/
def liftTarget (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) {Test : Type*}
    (kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (τ : Test) (n : ℕ) :
    (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun x => metricTestGenerator minkowski (cfm (e n) x) (kOf τ x)

/-- The Cartan nondegeneracy floor `κ` of the `n`-th regulator coframe on `Ω`. -/
def CartanFloor (Ω : Opens (Fin 4 → ℝ)) (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) (n : ℕ)
    (κ : ℝ) : Prop :=
  ∀ᵐ x, x ∈ Ω → ∀ v : Fin 4 → Fin 4 → Fin 4 → ℝ, (∀ I μ ν, v I μ ν = -v I ν μ) →
    κ * ‖v‖ ≤ ‖PalatiniTorsionModel.cartan (coframeArr (e n) x) v‖

/-- The coframe noncollapse floor `c ≤ det e_X` of the `n`-th regulator coframe on `Ω`. -/
def CoframeFloor (Ω : Opens (Fin 4 → ℝ)) (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) (n : ℕ)
    (c : ℝ) : Prop :=
  ∀ᵐ x, x ∈ Ω → c ≤ (cfm (e n) x).det

theorem cartanFloor_mono {Ω : Opens (Fin 4 → ℝ)} {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {n : ℕ} : ∀ κ κ', CartanFloor Ω e n κ' → κ ≤ κ' → CartanFloor Ω e n κ :=
  fun _ _ h hle => h.mono fun _ hx hxΩ v hv =>
    (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hx hxΩ v hv)

theorem coframeFloor_mono {Ω : Opens (Fin 4 → ℝ)} {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {n : ℕ} : ∀ c c', CoframeFloor Ω e n c' → c ≤ c' → CoframeFloor Ω e n c :=
  fun _ _ h hle => h.mono fun _ hx hxΩ => hle.trans (hx hxΩ)

/-- **The certification procedure `(E1)`–`(E5)` applied to a selected cofinal sequence of finite
records** (`thm:main-einstein-alternative`).  Data: the records of `thm:main-renewal-einstein`
(scores, coframes, connections, curvature records, Cartan writer, represented torsion, physical
lifts, realized first variations of the reconstructed common action) on an open cylinder `Ω` with
a compact cylinder `K` and a determining test core.  The fields are

* the standing structure of the Lorentzian relational regulators (`mt:adm`) and the regularity of
  each finite record (finite local norms) — not certificates;
* the typed record data the certificates are computed from: the common-action curl/period
  defect, the resolved-memory defect, the binary face-subdivision defect (described in words in
  the manuscript), the endpoint cut graphs, the declared screens of the coframe and of the
  connection on every compact, the curvature propagation route on every compact, and (on the
  periodic branch) the literal-link route.

The certificates themselves are computed from these records in `cert`, `fullCert` and
`LiteralLinkRoute.cert`. -/
structure EinsteinCertificationProcedure (Ω : Opens (Fin 4 → ℝ))
    (score : ℕ → GravitationalClassDensity)
    (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) (t : Fin 4)
    (K : Set (Fin 4 → ℝ)) {Test : Type*}
    (kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (core : Set Test)
    (H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (δA : Test → ℕ → ℝ) where
  /-- Standing structure (`mt:adm`): metric-compatible Lorentz connections. -/
  connection_lorentz : ∀ n, ∀ᵐ x, x ∈ Ω → ∀ a,
    (minkowski * ω n a x)ᵀ = -(minkowski * ω n a x)
  /-- Standing structure: the represented torsion two-forms. -/
  torsion_rep : ∀ n (φ : 𝓓(Ω, ℝ)) a b,
    torsionPairing matAct (e n) (ω n) φ a b = ∫ x, φ x • T n a b x
  torsion_antisymm : ∀ n a b, ∀ᵐ x, x ∈ Ω → T n b a x = -T n a b x
  torsion_L2 : ∀ n a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (T n a b) 2 (volume.restrict C)
  /-- `K` is a compact spacetime cylinder of `Ω`. -/
  K_compact : IsCompact K
  K_subset : K ⊆ Ω
  /-- Regularity of the finite records: measurable, essentially bounded physical lifts. -/
  lift_measurable : ∀ τ ∈ core, ∀ n, AEStronglyMeasurable (H τ n) (volume.restrict K)
  lift_essBounded : ∀ τ ∈ core, ∀ n, eLpNorm (H τ n) ∞ (volume.restrict K) ≠ ∞
  /-- Regularity of the finite records: locally `L²` and `L⁶` coframes. -/
  coframe_L2 : ∀ n c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (e n c) 2 (volume.restrict C)
  coframe_L6 : ∀ n c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    eLpNorm (e n c) 6 (volume.restrict C) ≠ ∞
  /-- Regularity of the finite records: locally `L²` connections, `L³` spatial coefficients. -/
  connection_L2 : ∀ n a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (ω n a) 2 (volume.restrict C)
  connection_L3 : ∀ n a, a ≠ t → ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    eLpNorm (ω n a) 3 (volume.restrict C) ≠ ∞
  /-- Regularity of the finite records: locally `L²` curvature records. -/
  curvature_L2 : ∀ n a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (R n a b) 2 (volume.restrict C)
  /-- Typed record data: size of the common-action curl/period defect. -/
  curlPeriod : ℕ → ℝ
  /-- Typed record data: resolved-memory subtraction defect. -/
  memoryDefect : ℕ → ℝ
  /-- Typed record data: binary face-subdivision (face-linearity) defect. -/
  faceDefect : ℕ → ℝ
  /-- The endpoint cut graphs (`thm:main-spatial-screen`). -/
  cut : ℕ → EndpointCutRecord
  /-- The declared common-cylinder screens of the coframe on every compact. -/
  coframeScreens : ∀ (c : Fin 4) (C : CompactIn Ω),
    ScreenFamily (volume.restrict C.1) fun n => e n c
  /-- The declared common-cylinder screens of the connection on every compact. -/
  connectionScreens : ∀ (a : Fin 4) (C : CompactIn Ω),
    ScreenFamily (volume.restrict C.1) fun n => ω n a
  /-- The curvature propagation route on every compact. -/
  curvatureRoute : ∀ C : CompactIn Ω,
    CurvatureRoute fun n ab => (eLpNorm (R n ab.1 ab.2) 2 (volume.restrict C.1)).toReal
  /-- The periodic literal-link route, when the records are on that branch. -/
  literalLink : Option (LiteralLinkRoute Ω ω R t)

/-- The certificates common to both connection routes (the failure bank of
`subsec:supp-failed-certificates` minus the connection/curvature handoff). -/
inductive Item (Ω : Opens (Fin 4 → ℝ)) {Test : Type*} (core : Set Test)
  | curlPeriod | memory | faceLinearity | naturality
  | firstVariation (τ : core) | remainder (τ : core) | liftConsistency (τ : core)
  | liftBudget (τ : core)
  | holstCalibration | palatiniCalibration | volumeCalibration | palatiniNormalization
  | euler (C : CompactIn Ω) | cartanMargin | cutMargin
  | coframeTail (c : Fin 4) (C : CompactIn Ω) | coframeComparison (c : Fin 4) (C : CompactIn Ω) (R : ℕ)
  | coframeL6 (c : Fin 4) (C : CompactIn Ω) | coframeMargin
  | curvature (C : CompactIn Ω) (i : CurvatureItem)

/-- The certificates of the full-connection route of `(E5)`. -/
inductive FullItem (Ω : Opens (Fin 4 → ℝ)) (t : Fin 4)
  | connectionTail (a : Fin 4) (C : CompactIn Ω)
  | connectionComparison (a : Fin 4) (C : CompactIn Ω) (R : ℕ)
  | connectionL3 (a : Fin 4) (ha : a ≠ t) (C : CompactIn Ω)
  | cartanCurvature (φ : 𝓓(Ω, ℝ)) (a b i j : Fin 4)
  | cartanIncidence (φ : 𝓓(Ω, ℝ)) (a b i j : Fin 4)

namespace EinsteinCertificationProcedure

variable {Ω : Opens (Fin 4 → ℝ)} {score : ℕ → GravitationalClassDensity}
  {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {t : Fin 4} {K : Set (Fin 4 → ℝ)}
  {Test : Type*} {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {core : Set Test}
  {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {δA : Test → ℕ → ℝ}

/-- **The common certificates, computed from the records**: common-action curl/period (finite
algebraic), memory subtraction (finite algebraic), face linearity (summability budget), Lorentz
naturality of the classified score (finite algebraic); realized metric first variation
(residual), physical first-variation remainder `eq:main-first-variation-reduction` (residual),
consistency of the physical lifts with the inverse-metric test lift (residual, in `L^∞(K)`),
uniform lift bound (budget); calibrated Holst/Palatini/volume coefficients (comparisons),
Palatini normalization (margin); spinless connection Euler residual = torsion defect (residual,
`L²` on every compact), Cartan nondegeneracy (margin), efficient cut margin `I^eff_X` (margin);
common-cylinder coframe tails and transported-screen comparisons, `L⁶` coframe budget, coframe
noncollapse (margin); curvature propagation budgets and interpolation stability. -/
def cert (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA) :
    Item Ω core → Certificate
  | .curlPeriod => .algebraic fun n => P.curlPeriod n = 0
  | .memory => .algebraic fun n => P.memoryDefect n = 0
  | .faceLinearity => .budget fun n => ∑ i ∈ Finset.range n, |P.faceDefect i|
  | .naturality => .algebraic fun n => (score n).IsLorentzNatural
  | .firstVariation τ => .residual (δA τ.1)
  | .remainder τ => .residual (classifiedVariationRemainder (δA τ.1)
      (fun n => realizedHolst K (e n) (H τ.1 n) (R n))
      (fun n => realizedPalatini K (e n) (H τ.1 n) (R n))
      (fun n => realizedVolume K (e n) (H τ.1 n))
      (fun n => holstCoeff (score n)) (fun n => palatiniCoeff (score n))
      (fun n => volumeCoeff (score n)))
  | .liftConsistency τ => .residual fun n =>
      trunc (eLpNorm (H τ.1 n - liftTarget e kOf τ.1 n) ∞ (volume.restrict K))
  | .liftBudget τ => .budget fun n => (eLpNorm (H τ.1 n) ∞ (volume.restrict K)).toReal
  | .holstCalibration => .comparison fun m n => |holstCoeff (score m) - holstCoeff (score n)|
  | .palatiniCalibration => .comparison fun m n =>
      |palatiniCoeff (score m) - palatiniCoeff (score n)|
  | .volumeCalibration => .comparison fun m n => |volumeCoeff (score m) - volumeCoeff (score n)|
  | .palatiniNormalization => .margin fun n => |palatiniCoeff (score n)|
  | .euler C => .residual fun n => trunc (eLpNorm (eulerResidualRep (holstCoeff (score n))
      (palatiniCoeff (score n)) (e n) (T n)) 2 (volume.restrict C.1))
  | .cartanMargin => .margin fun n => cappedMargin (CartanFloor Ω e n)
  | .cutMargin => .margin fun n => (P.cut n).margin
  | .coframeTail c C => (P.coframeScreens c C).tailCert
  | .coframeComparison c C R => (P.coframeScreens c C).comparisonCert R
  | .coframeL6 c C => .budget fun n => (eLpNorm (e n c) 6 (volume.restrict C.1)).toReal
  | .coframeMargin => .margin fun n => cappedMargin (CoframeFloor Ω e n)
  | .curvature C i => (P.curvatureRoute C).cert i

/-- **The full-connection certificates, computed from the records**: common-cylinder connection
tails and transported-screen comparisons (`ass:main-connection-compactness`), the uniform spatial
`L³` connection budget (the disclosed amendment, `eq:main-connection-hodge-budget`), and the
entries of the Cartan curvature mismatch `𝔠_X` (`eq:main-cartan-curvature-residual`) and of the
Cartan/interface incidence mismatch `𝔍_X` (`eq:main-cartan-incidence`; the distributional
derivative carries every interface contribution) for the finite Cartan writer `W`. -/
def fullCert (_P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA) :
    FullItem Ω t → Certificate
  | .connectionTail a C => (_P.connectionScreens a C).tailCert
  | .connectionComparison a C R => (_P.connectionScreens a C).comparisonCert R
  | .connectionL3 a _ C => .budget fun n => (eLpNorm (ω n a) 3 (volume.restrict C.1)).toReal
  | .cartanCurvature φ a b i j => .residual fun n =>
      ((∫ x, φ x • R n a b x) - ∫ x, φ x • W n a b x) i j
  | .cartanIncidence φ a b i j => .residual fun n =>
      ((∫ x, φ x • W n a b x) - curvaturePairing (ω n) φ a b) i j

theorem cert_admissible (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA)
    (i : Item Ω core) : (P.cert i).Admissible := by
  cases i with
  | coframeTail c C => exact (P.coframeScreens c C).tailCert_admissible
  | curvature C i => exact (P.curvatureRoute C).cert_admissible i
  | _ => exact True.intro

theorem fullCert_admissible
    (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA)
    (i : FullItem Ω t) : (P.fullCert i).Admissible := by
  cases i with
  | connectionTail a C => exact (P.connectionScreens a C).tailCert_admissible
  | _ => exact True.intro

theorem literalCert_admissible (L : LiteralLinkRoute Ω ω R t) (i : LiteralItem) :
    (L.cert i).Admissible := by
  cases i <;> exact True.intro

/-- The procedure passes: every common certificate passes, and the connection/curvature handoff
passes on the full-connection route or on the literal-link route. -/
def Passes (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA) : Prop :=
  (∀ i, (P.cert i).Passes) ∧
    ((∀ i, (P.fullCert i).Passes) ∨
      ∃ L, P.literalLink = some L ∧ ∀ i, (L.cert i).Passes)

/-- The failure witness: a common certificate fails with its cofinal witness, or the
full-connection route fails with a cofinal witness and so does the literal-link route whenever
the records are on that branch. -/
def FailureWitness (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA) :
    Prop :=
  (∃ i, (P.cert i).Witness) ∨
    ((∃ i, (P.fullCert i).Witness) ∧
      ∀ L, P.literalLink = some L → ∃ i, (L.cert i).Witness)

/-- The failure branch of the alternative: either the procedure passes or it fails with a
cofinal witness. -/
theorem passes_or_failureWitness
    (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA) :
    P.Passes ∨ P.FailureWitness := by
  rcases forall_passes_or_exists_witness P.cert P.cert_admissible with hc | hc
  · rcases forall_passes_or_exists_witness P.fullCert P.fullCert_admissible with hf | hf
    · exact Or.inl ⟨hc, Or.inl hf⟩
    · cases hL : P.literalLink with
      | none => exact Or.inr (Or.inr ⟨hf, fun L h => by rw [hL] at h; cases h⟩)
      | some L =>
        rcases forall_passes_or_exists_witness L.cert (literalCert_admissible L) with hl | hl
        · exact Or.inl ⟨hc, Or.inr ⟨L, hL, hl⟩⟩
        · exact Or.inr (Or.inr ⟨hf, fun L' h => by
            rw [hL, Option.some.injEq] at h; subst h; exact hl⟩)
  · exact Or.inr (Or.inl hc)

/-- The witnesses genuinely obstruct the procedure. -/
theorem not_passes_of_failureWitness
    (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA)
    (hw : P.FailureWitness) : ¬P.Passes := by
  rintro ⟨hc, hr⟩
  rcases hw with ⟨i, hi⟩ | ⟨⟨i, hi⟩, hL⟩
  · exact (P.cert i).not_passes_of_witness hi (hc i)
  · rcases hr with hf | ⟨L, hL', hl⟩
    · exact (P.fullCert i).not_passes_of_witness hi (hf i)
    · obtain ⟨j, hj⟩ := hL L hL'
      exact (L.cert j).not_passes_of_witness hj (hl j)

end EinsteinCertificationProcedure

end Procedure

/-! ### Passing certificates give the certification packet `(E1)`–`(E5)` -/

section Positive

open DistributionalTorsion DistributionalCurvature LimitEinsteinInsertion PalatiniEinsteinAlgebra
  RenewalPalatiniHandoff RenewalEinstein

/-- Pointwise convergence of the coframe one-forms gives convergence of the coframe matrices. -/
theorem tendsto_cfm {u : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {v : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {x : Fin 4 → ℝ} (h : ∀ c, Tendsto (fun j => u j c x) atTop (𝓝 (v c x))) :
    Tendsto (fun j => cfm (u j) x) atTop (𝓝 (cfm v x)) := by
  simp only [cfm, coframeMatrix]
  refine tendsto_pi_nhds.2 fun I => tendsto_pi_nhds.2 fun μ => ?_
  exact (continuous_apply I).continuousAt.tendsto.comp (h μ)

theorem continuous_metricTestGenerator_coframe (k : Matrix (Fin 4) (Fin 4) ℝ) :
    Continuous fun E : Matrix (Fin 4) (Fin 4) ℝ => metricTestGenerator minkowski E k := by
  unfold metricTestGenerator coframeMetric
  fun_prop

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The full-connection certificate passes to subsequences. -/
theorem fullConnectionCertificate_comp {Ω : Opens (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4}
    (h : FullConnectionCertificate Ω ω R W ωL t) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    FullConnectionCertificate Ω (fun n => ω (φ n)) (fun n => R (φ n)) (fun n => W (φ n)) ωL t :=
  { connection_L2 := l2LocTendsto_comp h.connection_L2 hφ
    spatialConnectionL3Bound := fun a ha C hC hCΩ => by
      obtain ⟨M, hM, hb⟩ := h.spatialConnectionL3Bound a ha C hC hCΩ
      exact ⟨M, hM, fun n => hb (φ n)⟩
    cartanCurvatureResidual := fun ψ a b =>
      (h.cartanCurvatureResidual ψ a b).comp hφ.tendsto_atTop
    cartanIncidenceResidual := fun ψ a b =>
      (h.cartanIncidenceResidual ψ a b).comp hφ.tendsto_atTop }

/-- The literal-link certificate passes to subsequences. -/
theorem literalLinkCertificate_comp {Ω : Opens (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4}
    (h : LiteralLinkCertificate Ω ω R ωL RL t) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    LiteralLinkCertificate Ω (fun n => ω (φ n)) (fun n => R (φ n)) ωL RL t :=
  { spatialConnectionL3Bound := fun a ha C hC hCΩ => by
      obtain ⟨M, hM, hb⟩ := h.spatialConnectionL3Bound a ha C hC hCΩ
      exact ⟨M, hM, fun n => hb (φ n)⟩
    connection_L2 := fun n => h.connection_L2 (φ n)
    connection_bound := fun a C hC hCΩ => by
      obtain ⟨M, hM, hb⟩ := h.connection_bound a C hC hCΩ
      exact ⟨M, hM, fun n => hb (φ n)⟩
    connection_limit_L2 := h.connection_limit_L2
    connection_weak := fun a C hC hCΩ g hg =>
      (h.connection_weak a C hC hCΩ g hg).comp hφ.tendsto_atTop
    spatial_strong := fun a ha C hC hCΩ =>
      ⟨fun n => (h.spatial_strong a ha C hC hCΩ).memLp (φ n),
        (h.spatial_strong a ha C hC hCΩ).memLp_lim,
        (h.spatial_strong a ha C hC hCΩ).tendsto.comp hφ.tendsto_atTop⟩
    curvature_limit_L2 := h.curvature_limit_L2
    curvature_weak := fun a b C hC hCΩ g hg =>
      (h.curvature_weak a b C hC hCΩ g hg).comp hφ.tendsto_atTop
    curvature_identified := h.curvature_identified }

namespace EinsteinCertificationProcedure

variable {Ω : Opens (Fin 4 → ℝ)} {score : ℕ → GravitationalClassDensity}
  {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {t : Fin 4} {K : Set (Fin 4 → ℝ)}
  {Test : Type*} {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {core : Set Test}
  {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {δA : Test → ℕ → ℝ}

/-- The connection/curvature handoff of `(E5)` from the passing route certificates: after a
subsequence (the identity on the full-connection route), either the full-connection certificate
or the literal-link certificate holds. -/
theorem connectionRoute_of_passes
    (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA)
    (hroute : (∀ i, (P.fullCert i).Passes) ∨
      ∃ L, P.literalLink = some L ∧ ∀ i, (L.cert i).Passes) :
    ∃ φ0 : ℕ → ℕ, StrictMono φ0 ∧ ∃ ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
      FullConnectionCertificate Ω (fun n => ω (φ0 n)) (fun n => R (φ0 n)) (fun n => W (φ0 n)) ωL t ∨
        ∃ RL, LiteralLinkCertificate Ω (fun n => ω (φ0 n)) (fun n => R (φ0 n)) ωL RL t := by
  rcases hroute with hF | ⟨L, -, hL⟩
  · obtain ⟨ωL, hωL, -⟩ := exists_l2LocTendsto_of_cauchy Ω ω P.connection_L2
      fun a C hC hCΩ => (P.connectionScreens a ⟨C, hC, hCΩ⟩).cauchy
        (fun n => (P.connection_L2 n a C hC hCΩ).1) (hF (.connectionTail a ⟨C, hC, hCΩ⟩))
        (fun Rr => hF (.connectionComparison a ⟨C, hC, hCΩ⟩ Rr))
    refine ⟨id, strictMono_id, ωL, Or.inl
      { connection_L2 := hωL
        spatialConnectionL3Bound := fun a ha C hC hCΩ =>
          exists_bound_of_budget_passes (fun n => P.connection_L3 n a ha C hC hCΩ)
            (hF (.connectionL3 a ha ⟨C, hC, hCΩ⟩))
        cartanCurvatureResidual := fun φ a b => ?_
        cartanIncidenceResidual := fun φ a b => ?_ }⟩
    · exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
        hF (.cartanCurvature φ a b i j)
    · exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
        hF (.cartanIncidence φ a b i j)
  · obtain ⟨φ0, hφ0, ωL, RL, hLL⟩ := L.compactness (hL .chart) (hL .energy)
    exact ⟨φ0, hφ0, ωL, Or.inr ⟨RL, hLL⟩⟩

/-- **Passing certificates give `(E1)`–`(E5)`** (`thm:main-einstein-alternative`, positive
branch): if every certificate of the procedure passes on a cofinal tail, then along a subsequence
of the selected sequence there are a limit coframe `e`, a limit connection `ω`, calibrated
coefficients `(α, β, λ)` and lift bounds `M` for which the records satisfy the certification
packet `RenewalEinsteinCertification` of `thm:main-renewal-einstein`.  The limits are produced:
`(α, β, λ)` from the calibrated comparisons (completeness of `ℝ`), `e` and `ω` from the
common-cylinder tails and transported-screen comparisons (compact-screen upgrade and completeness
of `L²_loc`), the nondegeneracy of `e` and of the Cartan map from the margins, the uniform bounds
from the budgets (the curvature bound through the propagation certificates
`thm:main-curvature-propagation` / `thm:main-discrete-curvature`). -/
theorem certification_of_passes
    (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA) (hP : P.Passes) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
      (ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (α β lam : ℝ) (M : Test → ℝ),
      RenewalEinsteinCertification Ω (fun n => score (ψ n)) (fun n => e (ψ n))
        (fun n => ω (ψ n)) (fun n => R (ψ n)) (fun n => W (ψ n)) (fun n => T (ψ n)) eL ωL α β lam
        t K kOf core (fun τ n => H τ (ψ n)) M (fun τ n => δA τ (ψ n)) := by
  obtain ⟨hc, hroute⟩ := hP
  -- (E1) realized first variations and (E2) physical first-variation remainders
  have hδA : ∀ τ ∈ core, Tendsto (δA τ) atTop (𝓝 0) := fun τ hτ => hc (.firstVariation ⟨τ, hτ⟩)
  -- (E3) calibrated coefficients and the Palatini normalization
  obtain ⟨α, hα⟩ := exists_tendsto_of_comparison_passes (hc .holstCalibration)
  obtain ⟨β, hβ⟩ := exists_tendsto_of_comparison_passes (hc .palatiniCalibration)
  obtain ⟨lam, hlam⟩ := exists_tendsto_of_comparison_passes (hc .volumeCalibration)
  have hβ0 : β ≠ 0 := ne_zero_of_margin_passes (hc .palatiniNormalization) hβ
  -- (E3) eventual Cartan floor, (E2) eventual naturality, (E4) eventual coframe floor
  obtain ⟨cC, hcC, hCev⟩ : ∃ c > 0, ∀ᶠ n in atTop, c ≤ cappedMargin (CartanFloor Ω e n) :=
    hc .cartanMargin
  obtain ⟨cD, hcD, hDev⟩ : ∃ c > 0, ∀ᶠ n in atTop, c ≤ cappedMargin (CoframeFloor Ω e n) :=
    hc .coframeMargin
  have hnat : ∀ᶠ n in atTop, (score n).IsLorentzNatural := hc .naturality
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hCev.and (hnat.and hDev))
  have hfloorC : ∀ n ≥ N, CartanFloor Ω e n (cC / 2) := fun n hn =>
    of_le_cappedMargin cartanFloor_mono hcC (hN n hn).1
  have hfloorD : ∀ n ≥ N, CoframeFloor Ω e n (cD / 2) := fun n hn =>
    of_le_cappedMargin coframeFloor_mono hcD (hN n hn).2.2
  -- (E1) uniform lift bounds
  have hliftB : ∀ τ ∈ core, ∃ B, 0 ≤ B ∧ ∀ n, ∀ᵐ x ∂(volume.restrict K), ‖H τ n x‖ ≤ B := by
    intro τ hτ
    obtain ⟨B, hB⟩ : BddAbove (Set.range fun n =>
        (eLpNorm (H τ n) ∞ (volume.restrict K)).toReal) := hc (.liftBudget ⟨τ, hτ⟩)
    have hB0 : 0 ≤ B := ENNReal.toReal_nonneg.trans (hB ⟨0, rfl⟩)
    refine ⟨B, hB0, fun n => ae_norm_le_of_eLpNorm_top_le hB0 ?_⟩
    rw [← ENNReal.ofReal_toReal (P.lift_essBounded τ hτ n)]
    exact ENNReal.ofReal_le_ofReal (hB ⟨n, rfl⟩)
  choose! Mτ hMτ0 hMτ using hliftB
  -- (E1) consistency of the lifts with the inverse-metric test lift
  have hcons : ∀ τ ∈ core, ∀ᵐ x ∂(volume.restrict K),
      Tendsto (fun n => H τ n x - liftTarget e kOf τ n x) atTop (𝓝 0) := fun τ hτ =>
    ae_tendsto_zero_of_eLpNorm_top (tendsto_trunc_iff.1 (hc (.liftConsistency ⟨τ, hτ⟩)))
  -- (E4) coframe Cauchy comparison on every compact (compact-screen upgrade)
  have hcauE : ∀ c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N, ∀ m ≥ N, ∀ n ≥ N, eLpNorm (e m c - e n c) 2 (volume.restrict C) < ε :=
    fun c C hC hCΩ => (P.coframeScreens c ⟨C, hC, hCΩ⟩).cauchy
      (fun n => (P.coframe_L2 n c C hC hCΩ).1) (hc (.coframeTail c ⟨C, hC, hCΩ⟩))
      (fun Rr => hc (.coframeComparison c ⟨C, hC, hCΩ⟩ Rr))
  -- (E4) `L⁶` budget
  have hL6 : ∀ c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (e n c) 6 (volume.restrict C) ≤ M :=
    fun c C hC hCΩ => exists_bound_of_budget_passes (fun n => P.coframe_L6 n c C hC hCΩ)
      (hc (.coframeL6 c ⟨C, hC, hCΩ⟩))
  -- (E5) curvature bound from the propagation certificates
  have hcurv : ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ n a b, eLpNorm (R n a b) 2 (volume.restrict C) ≤ B := by
    intro C hC hCΩ
    obtain ⟨B, hB⟩ := (P.curvatureRoute ⟨C, hC, hCΩ⟩).bounded
      (fun i => hc (.curvature ⟨C, hC, hCΩ⟩ i))
    refine ⟨ENNReal.ofReal B, ENNReal.ofReal_ne_top, fun n a b => ?_⟩
    rw [← ENNReal.ofReal_toReal (P.curvature_L2 n a b C hC hCΩ).2.ne]
    exact ENNReal.ofReal_le_ofReal (hB n (a, b))
  -- (E5) connection handoff, then the coframe limit along a further subsequence
  obtain ⟨φ0, hφ0, ωL, hroute'⟩ := P.connectionRoute_of_passes hroute
  obtain ⟨eL, heL, φ1, hφ1, hae⟩ := exists_l2LocTendsto_of_cauchy Ω (fun n => e (φ0 n))
    (fun n => P.coframe_L2 (φ0 n)) fun c C hC hCΩ ε hε => by
      obtain ⟨M, hM⟩ := hcauE c C hC hCΩ ε hε
      exact ⟨M, fun m hm n hn => hM (φ0 m) (hm.trans (hφ0.id_le m)) (φ0 n)
        (hn.trans (hφ0.id_le n))⟩
  set χ : ℕ → ℕ := fun j => φ1 (j + N) with hχ
  have hχmono : StrictMono χ := hφ1.comp fun a b h => by omega
  set ψ : ℕ → ℕ := fun j => φ0 (χ j) with hψdef
  have hψ : StrictMono ψ := hφ0.comp hχmono
  have hψN : ∀ j, N ≤ ψ j := fun j =>
    le_trans (by omega : N ≤ j + N) ((hφ1.id_le (j + N)).trans (hφ0.id_le (φ1 (j + N))))
  -- a.e. convergence of the coframes along `ψ`
  have haeψ : ∀ᵐ x, x ∈ Ω → ∀ c, Tendsto (fun j => e (ψ j) c x) atTop (𝓝 (eL c x)) := by
    filter_upwards [hae] with x hx hxΩ c
    exact (hx hxΩ c).comp ((tendsto_add_atTop_iff_nat N).2 tendsto_id)
  refine ⟨ψ, hψ, eL, ωL, α, β, lam, Mτ, ?_⟩
  exact
    { connection_lorentz := fun n => P.connection_lorentz (ψ n)
      torsion_rep := fun n => P.torsion_rep (ψ n)
      torsion_antisymm := fun n => P.torsion_antisymm (ψ n)
      torsion_L2 := fun n => P.torsion_L2 (ψ n)
      e1_compact := P.K_compact
      e1_subset := P.K_subset
      e1_firstVariation_vanish := fun τ hτ => (hδA τ hτ).comp hψ.tendsto_atTop
      e1_lift_measurable := fun τ hτ n => P.lift_measurable τ hτ (ψ n)
      e1_lift_bounded := fun τ hτ n => hMτ τ hτ (ψ n)
      e1_lift_tendsto := fun τ hτ => by
        have hK : ∀ᵐ x ∂(volume.restrict K), ∀ c,
            Tendsto (fun j => e (ψ j) c x) atTop (𝓝 (eL c x)) :=
          (ae_restrict_iff' P.K_compact.measurableSet).2
            (haeψ.mono fun x hx hxK => hx (P.K_subset hxK))
        filter_upwards [hK, hcons τ hτ] with x hx hx'
        have h1 : Tendsto (fun j => liftTarget e kOf τ (ψ j) x) atTop
            (𝓝 (metricTestGenerator minkowski (cfm eL x) (kOf τ x))) :=
          ((continuous_metricTestGenerator_coframe (kOf τ x)).tendsto _).comp (tendsto_cfm hx)
        have h2 := (hx'.comp hψ.tendsto_atTop).add h1
        simpa using h2
      e2_classified := fun n => (hN (ψ n) (hψN n)).2.1
      e2_firstVariationRemainder := fun τ hτ =>
        (hc (.remainder ⟨τ, hτ⟩)).comp hψ.tendsto_atTop
      e3_holst_tendsto := hα.comp hψ.tendsto_atTop
      e3_palatini_tendsto := hβ.comp hψ.tendsto_atTop
      e3_volume_tendsto := hlam.comp hψ.tendsto_atTop
      e3_palatini_ne_zero := hβ0
      e3_euler_residual_tendsto := fun C hC hCΩ =>
        (tendsto_trunc_iff.1 (hc (.euler ⟨C, hC, hCΩ⟩))).comp hψ.tendsto_atTop
      e3_cartan_floor := ⟨cC / 2, by positivity, fun n => hfloorC (ψ n) (hψN n)⟩
      e4_coframe_L2 := l2LocTendsto_comp heL hχmono
      e4_coframe_L6 := fun c C hC hCΩ => by
        obtain ⟨M, hM, hb⟩ := hL6 c C hC hCΩ
        exact ⟨M, hM, fun n => hb (ψ n)⟩
      e4_coframe_oriented := fun n => (hfloorD (ψ n) (hψN n)).mono fun x hx hxΩ =>
        lt_of_lt_of_le (by positivity) (hx hxΩ)
      e4_limit_nondegenerate := by
        have hall : ∀ᵐ x, ∀ j, x ∈ Ω → cD / 2 ≤ (cfm (e (ψ j)) x).det :=
          ae_all_iff.2 fun j => hfloorD (ψ j) (hψN j)
        filter_upwards [hall, haeψ] with x hx hx' hxΩ
        have hdet : Tendsto (fun j => (cfm (e (ψ j)) x).det) atTop (𝓝 (cfm eL x).det) :=
          ((continuous_id.matrix_det).tendsto _).comp (tendsto_cfm (hx' hxΩ))
        have : cD / 2 ≤ (cfm eL x).det :=
          ge_of_tendsto hdet (Eventually.of_forall fun j => hx j hxΩ)
        exact (lt_of_lt_of_le (by positivity) this).ne'
      e5_curvature_L2 := fun n => P.curvature_L2 (ψ n)
      e5_curvature_bound := fun C hC hCΩ => by
        obtain ⟨B, hB, hb⟩ := hcurv C hC hCΩ
        exact ⟨B, hB, fun n => hb (ψ n)⟩
      e5_connection_route := by
        rcases hroute' with hF | ⟨RL, hL⟩
        · exact Or.inl (fullConnectionCertificate_comp hF hχmono)
        · exact Or.inr ⟨RL, literalLinkCertificate_comp hL hχmono⟩ }

end EinsteinCertificationProcedure

end Positive

/-! ### `thm:main-einstein-alternative` -/

section Alternative

open DistributionalTorsion DistributionalCurvature LimitEinsteinInsertion PalatiniEinsteinAlgebra
  RenewalPalatiniHandoff RenewalEinstein

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace EinsteinCertificationProcedure

variable {Ω : Opens (Fin 4 → ℝ)} {score : ℕ → GravitationalClassDensity}
  {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {t : Fin 4} {K : Set (Fin 4 → ℝ)}
  {Test : Type*} {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {core : Set Test}
  {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {δA : Test → ℕ → ℝ}

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- The Einstein conclusion of `thm:main-renewal-einstein` for a certified packet (wrapper, so
that this file does not depend on the exact shape of that conclusion). -/
theorem einsteinConclusion_of_certification [TopologicalSpace Test]
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {α β lam : ℝ} {M : Test → ℝ}
    (h : RenewalEinsteinCertification Ω score e ω R W T eL ωL α β lam t K kOf core H M δA) :
    EinsteinCertificationConclusion Ω eL ωL β lam K kOf core δA := by
  first
    | exact renewal_einstein_certification h
    | exact (renewal_einstein_certification h).1
    | exact (renewal_einstein_certification h).2

/-- **`thm:main-einstein-alternative` (Einstein limit or failed certificate).**  Apply the finite
certification procedure `(E1)`–`(E5)` to a selected cofinal sequence of finite records of a
complete gravitational renewal cylinder.  Exactly one of the following holds.

* The certificates pass on a cofinal tail (`P.Passes`).  Then a subsequence of the selected
  sequence satisfies the certification packet of `thm:main-renewal-einstein` with produced limits
  `(e, ω, α, β, λ)`, and hence has its Einstein limit: zero limiting torsion, `χ = β ≠ 0`,
  identified Levi-Civita curvature, the metric first variations converge to
  `χ ∫_K √(-g) (G + Λ g) k`, and `G + Λ g = 0` on the determining core and its closure
  (`EinsteinCertificationConclusion`).
* The procedure fails (`¬P.Passes`), and the failure is retained on the same records with its
  cofinal witness (`P.FailureWitness`): an algebraic defect (curl/period, memory, naturality,
  literal-link chart) on cofinally many records, a residual bounded below by `ε > 0` along a
  subsequence (realized metric variation, first-variation remainder, lift consistency, Euler/
  torsion defect, Cartan or interface mismatch), an unbounded budget along a subsequence (face
  subdivision, lift, `L⁶` coframe, spatial `L³` connection, initial/growth/transfer/source/duration/
  lapse/interpolation budgets, literal-link energy), a failed positive margin below `1/(k+1)`
  along a subsequence (Palatini normalization, Cartan nondegeneracy, efficient cut margin,
  coframe noncollapse, discrete step margin), a compactness tail with arbitrarily late records
  outside arbitrarily large screens, or separated pairs of records in a calibrated comparison
  (coupling calibration, transported-screen comparisons).  On the connection handoff the
  failure is witnessed on the full-connection route and, for records on the periodic branch,
  also on the literal-link route.

Failure is an obstruction to this sufficient procedure, not a proof that no subsequence has an
Einstein limit. -/
theorem einstein_limit_or_failed_certificate [TopologicalSpace Test]
    (P : EinsteinCertificationProcedure Ω score e ω R W T t K kOf core H δA) :
    (P.Passes ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
        (ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (α β lam : ℝ) (M : Test → ℝ),
        RenewalEinsteinCertification Ω (fun n => score (ψ n)) (fun n => e (ψ n))
          (fun n => ω (ψ n)) (fun n => R (ψ n)) (fun n => W (ψ n)) (fun n => T (ψ n)) eL ωL α β
          lam t K kOf core (fun τ n => H τ (ψ n)) M (fun τ n => δA τ (ψ n)) ∧
        EinsteinCertificationConclusion Ω eL ωL β lam K kOf core (fun τ n => δA τ (ψ n))) ∨
      (¬P.Passes ∧ P.FailureWitness) := by
  rcases P.passes_or_failureWitness with hp | hw
  · obtain ⟨ψ, hψ, eL, ωL, α, β, lam, M, hcert⟩ := P.certification_of_passes hp
    exact Or.inl ⟨hp, ψ, hψ, eL, ωL, α, β, lam, M, hcert,
      einsteinConclusion_of_certification hcert⟩
  · exact Or.inr ⟨P.not_passes_of_failureWitness hw, hw⟩

end EinsteinCertificationProcedure

/-! ### Non-vacuity: a passing flat procedure and a failing one -/

theorem trunc_eLpNorm_sub_self {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (f : X → E) (p : ℝ≥0∞) (μ : Measure X) : trunc (eLpNorm (f - f) p μ) = 0 := by
  simp [trunc]

theorem trunc_eLpNorm_zero {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (p : ℝ≥0∞) (μ : Measure X) : trunc (eLpNorm (0 : X → E) p μ) = 0 := by
  simp [trunc]

/-- A discrete propagation record with no steps, for curvature records of size at most `B`. -/
def DiscretePropagationRecord.ofBounded {κ : Type*} (q : κ → ℝ) (B : ℝ) (hq : ∀ i, q i ≤ B) :
    DiscretePropagationRecord q where
  V := ℝ
  steps := 0
  s _ := 0
  a _ := 0
  d _ := 0
  K _ := 0
  L _ := 0
  Tr _ := 0
  Y _ := 0
  ε _ := 0
  b := 0
  b_lt_one := one_pos
  s_pos _ h := absurd h (Nat.not_lt_zero _)
  a_nonneg _ h := absurd h (Nat.not_lt_zero _)
  d_nonneg _ h := absurd h (Nat.not_lt_zero _)
  skew _ h := absurd h (Nat.not_lt_zero _)
  growth _ h := absurd h (Nat.not_lt_zero _)
  transfer _ h := absurd h (Nat.not_lt_zero _)
  step_bound _ h := absurd h (Nat.not_lt_zero _)
  update _ h := absurd h (Nat.not_lt_zero _)
  CI := 0
  Cζ := B
  CI_nonneg := le_rfl
  slice _ _ i := by simpa using hq i

/-- The two-point endpoint cut record with conductance `ε` (efficient cut constant `ε`). -/
def twoPointCut (ε : ℝ) (hε : 0 ≤ ε) : EndpointCutRecord where
  V := Fin 2
  graph := SpatialScreenTwoPoint.twoPoint ε hε
  capacity := (SpatialScreenTwoPoint.twoPoint ε hε).conductance

theorem twoPointCut_margin (ε : ℝ) (hε : 0 ≤ ε) : (twoPointCut ε hε).margin = ε :=
  SpatialScreenTwoPoint.efficientCutConstant_twoPoint ε hε

/-- The flat records (Minkowski coframe, zero connection, curvature, torsion and Cartan writer,
Palatini score, constant inverse-metric tests, zero realized variations) with identity screens,
the trivial discrete propagation route, and a given sequence of endpoint cut records. -/
def flatProcedure (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) (cut : ℕ → EndpointCutRecord) :
    EinsteinCertificationProcedure ⊤ (fun _ => RenewalGeometry.palatiniDensity)
      (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ _ => 0) (fun _ _ _ _ => 0)
      (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) 0 K (Test := Matrix (Fin 4) (Fin 4) ℝ)
      (fun k _ => k) Set.univ (fun k _ _ => metricTestGenerator minkowski 1 k)
      (fun _ _ => 0) where
  connection_lorentz := (renewalEinsteinCertification_flat K hK).connection_lorentz
  torsion_rep := (renewalEinsteinCertification_flat K hK).torsion_rep
  torsion_antisymm := (renewalEinsteinCertification_flat K hK).torsion_antisymm
  torsion_L2 := (renewalEinsteinCertification_flat K hK).torsion_L2
  K_compact := hK
  K_subset := Set.subset_univ K
  lift_measurable := (renewalEinsteinCertification_flat K hK).e1_lift_measurable
  lift_essBounded _ _ _ := (memLp_top_const _).eLpNorm_lt_top.ne
  coframe_L2 n c C hC hCΩ :=
    (renewalEinsteinCertification_flat K hK).e4_coframe_L2.memLp n c C hC hCΩ
  coframe_L6 n c C hC hCΩ := by
    obtain ⟨M, hM, hb⟩ := (renewalEinsteinCertification_flat K hK).e4_coframe_L6 c C hC hCΩ
    exact ne_top_of_le_ne_top hM (hb n)
  connection_L2 n a C hC hCΩ := renewalPalatiniHypotheses_flat.connection_L2.memLp n a C hC hCΩ
  connection_L3 n a ha C hC hCΩ := by
    obtain ⟨M, hM, hb⟩ := renewalPalatiniHypotheses_flat.spatialConnectionL3Bound a ha C hC hCΩ
    exact ne_top_of_le_ne_top hM (hb n)
  curvature_L2 := (renewalEinsteinCertification_flat K hK).e5_curvature_L2
  curlPeriod _ := 0
  memoryDefect _ := 0
  faceDefect _ := 0
  cut := cut
  coframeScreens c C := ScreenFamily.identity _ fun n =>
    ((renewalEinsteinCertification_flat K hK).e4_coframe_L2.memLp n c C.1 C.2.1 C.2.2).1
  connectionScreens _ _ := ScreenFamily.identity _ fun _ => aestronglyMeasurable_const
  curvatureRoute C := .discrete fun n => DiscretePropagationRecord.ofBounded _
    (Classical.choose ((renewalEinsteinCertification_flat K hK).e5_curvature_bound C.1 C.2.1
      C.2.2)).toReal fun ab => ENNReal.toReal_mono (Classical.choose_spec
        ((renewalEinsteinCertification_flat K hK).e5_curvature_bound C.1 C.2.1 C.2.2)).1
      ((Classical.choose_spec ((renewalEinsteinCertification_flat K hK).e5_curvature_bound C.1
        C.2.1 C.2.2)).2 n ab.1 ab.2)
  literalLink := none

theorem flat_cfm (x : Fin 4 → ℝ) :
    cfm (fun μ (_ : Fin 4 → ℝ) => (Pi.single μ 1 : Fin 4 → ℝ)) x = 1 :=
  coframeMatrix_basis

/-- **Non-vacuity, passing branch**: the flat procedure with the unit two-point endpoint graph
passes every certificate. -/
theorem flatProcedure_passes (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :
    (flatProcedure K hK fun _ => twoPointCut 1 zero_le_one).Passes := by
  have F := renewalEinsteinCertification_flat K hK
  have hβ1 : palatiniCoeff RenewalGeometry.palatiniDensity = 1 :=
    tendsto_const_nhds_iff.1 F.e3_palatini_tendsto
  refine ⟨fun i => ?_, Or.inl fun i => ?_⟩
  · cases i with
    | curlPeriod => exact Eventually.of_forall fun _ => rfl
    | memory => exact Eventually.of_forall fun _ => rfl
    | faceLinearity => exact ⟨0, by rintro _ ⟨n, rfl⟩; simp [flatProcedure]⟩
    | naturality => exact Eventually.of_forall fun n => F.e2_classified n
    | firstVariation τ => exact tendsto_const_nhds
    | remainder τ => exact F.e2_firstVariationRemainder τ.1 (Set.mem_univ _)
    | liftConsistency τ =>
      have h0 : ∀ n, (fun _ => metricTestGenerator minkowski 1 τ.1) -
          liftTarget (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun k _ => k) τ.1 n = 0 := by
        intro n; funext x; simp [liftTarget, flat_cfm]
      refine tendsto_const_nhds.congr fun n => ?_
      dsimp only
      rw [h0 n]
      exact (trunc_eLpNorm_zero _ _).symm
    | liftBudget τ => exact ⟨_, by rintro _ ⟨n, rfl⟩; exact le_rfl⟩
    | holstCalibration => exact fun ε hε => ⟨0, fun m _ n _ => by simpa using hε⟩
    | palatiniCalibration => exact fun ε hε => ⟨0, fun m _ n _ => by simpa using hε⟩
    | volumeCalibration => exact fun ε hε => ⟨0, fun m _ n _ => by simpa using hε⟩
    | palatiniNormalization =>
      exact ⟨1, one_pos, Eventually.of_forall fun n => by simp [hβ1]⟩
    | euler C => exact tendsto_trunc_iff.2 (F.e3_euler_residual_tendsto C.1 C.2.1 C.2.2)
    | cartanMargin =>
      obtain ⟨κ, hκ, hfl⟩ := F.e3_cartan_floor
      exact ⟨min κ 1, lt_min hκ one_pos, Eventually.of_forall fun n =>
        le_cappedMargin ⟨le_min hκ.le zero_le_one, min_le_right _ _⟩
          (cartanFloor_mono _ _ (hfl n) (min_le_left _ _))⟩
    | cutMargin =>
      exact ⟨1, one_pos, Eventually.of_forall fun n => (twoPointCut_margin 1 zero_le_one).ge⟩
    | coframeTail c C =>
      exact fun ε hε => ⟨0, fun n => (trunc_eLpNorm_sub_self _ _ _).le.trans hε.le⟩
    | coframeComparison c C R =>
      exact fun ε hε => ⟨0, fun m _ n _ => (trunc_eLpNorm_sub_self _ _ _).trans_lt hε⟩
    | coframeL6 c C => exact ⟨_, by rintro _ ⟨n, rfl⟩; exact le_rfl⟩
    | coframeMargin =>
      exact ⟨1, one_pos, Eventually.of_forall fun n =>
        le_cappedMargin ⟨zero_le_one, le_rfl⟩ (Eventually.of_forall fun x _ => by
          simp [flat_cfm])⟩
    | curvature C i =>
      cases i with
      | lapse => exact Certificate.trivial_passes
      | reconstruction =>
        exact ⟨(Classical.choose ((renewalEinsteinCertification_flat K hK).e5_curvature_bound
          C.1 C.2.1 C.2.2)).toReal, by rintro _ ⟨n, rfl⟩; exact le_rfl⟩
      | stepMargin =>
        exact ⟨1, one_pos, Eventually.of_forall fun n => by
          simp [DiscretePropagationRecord.ofBounded]⟩
      | _ =>
        exact ⟨0, by
          rintro _ ⟨n, rfl⟩
          simp [DiscretePropagationRecord.ofBounded, DiscretePropagationRecord.initialBudget,
            DiscretePropagationRecord.growthBudget, DiscretePropagationRecord.transferBudget,
            DiscretePropagationRecord.sourceBudget, DiscretePropagationRecord.durationBudget] <;>
          exact (norm_zero (E := ℝ)).le⟩
  · cases i with
    | connectionTail a C =>
      exact fun ε hε => ⟨0, fun n => (trunc_eLpNorm_sub_self _ _ _).le.trans hε.le⟩
    | connectionComparison a C R =>
      exact fun ε hε => ⟨0, fun m _ n _ => (trunc_eLpNorm_sub_self _ _ _).trans_lt hε⟩
    | connectionL3 a ha C => exact ⟨_, by rintro _ ⟨n, rfl⟩; exact le_rfl⟩
    | cartanCurvature φ a b i j => exact tendsto_const_nhds.congr fun n => by simp
    | cartanIncidence φ a b i j =>
      exact tendsto_const_nhds.congr fun n => by simp [curvaturePairing]

/-- The flat procedure has the Einstein limit (positive branch of the alternative). -/
example (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :=
  ((flatProcedure K hK fun _ => twoPointCut 1 zero_le_one).einstein_limit_or_failed_certificate
    ).resolve_right fun h => h.1 (flatProcedure_passes K hK)

/-- **Non-vacuity, failing branch**: with the collapsing two-point endpoint graphs
(conductance `1/(n+1)`, efficient cut constant `→ 0`) the procedure fails, and the cut margin
carries its cofinal witness. -/
theorem collapsingProcedure_fails (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :
    let P := flatProcedure K hK fun n => twoPointCut (1 / ((n : ℝ) + 1)) (by positivity)
    ¬P.Passes ∧ (P.cert .cutMargin).Witness := by
  intro P
  have hnot : ¬(P.cert .cutMargin).Passes := by
    rintro ⟨c, hc, hev⟩
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨n, hn1, hn2⟩ := (hev.and (hlim.eventually (gt_mem_nhds hc))).exists
    have : (twoPointCut (1 / ((n : ℝ) + 1)) (by positivity)).margin = 1 / ((n : ℝ) + 1) :=
      twoPointCut_margin _ _
    have h' : c ≤ 1 / ((n : ℝ) + 1) := by rw [← this]; exact hn1
    linarith
  exact ⟨fun h => hnot (h.1 .cutMargin),
    ((P.cert .cutMargin).passes_or_witness (P.cert_admissible _)).resolve_left hnot⟩

end Alternative

end RenewalGeometry.EinsteinAlternative
