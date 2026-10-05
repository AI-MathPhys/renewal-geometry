/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.RenewalInterfaceRealization
import RenewalGeometry.Continuum.EinsteinSMDiracStability
import RenewalGeometry.Continuum.EinsteinSMCofinalTransport

/-!
# Renewal Geometry realization (`cor:renewal-realization`, clause level)

`cor:renewal-realization`: on the source-native Standard-Model branch of
`prop:renewal-interface`, (i) the compactness, consistency and scaled-stationarity hypotheses of
`thm:main-limit` give a subsequential Einstein–Standard-Model limit; (ii) the additional
hypotheses of `cor:cofinal-unique` give a unique route-independent limit; (iii) for the explicit
local action the budgets of `thm:native-closure` give quantitative regularity, with cofinal
summability on the rate family of `cor:native-rate`.

* `RenewalBranch reg`: every interface of the regulator sequence is a renewal realization
  `renewalInterface n θ h hh` of `prop:renewal-interface` (`RenewalInterfaceRealization.lean`).
* `renewal_realization_limit` (clause (i)) and `renewal_realization_unique` (clause (ii)):
  composition of the branch with `DiracStab.main_limit_closed` (`thm:main-limit`) and `cofinal_unique`
  (`cor:cofinal-unique`), both proved.  As in the manuscript's proof, the branch enters only
  through the structural realization; the analytic hypotheses are those of the two theorems.
* Non-vacuity of the branch hypothesis: `renewalRegulator T θ n` is a regulator sequence
  (`def:regulator`) whose interfaces are the renewal realizations on `(ℤ/n)⁴` at the cutoffs
  `1/(k+1)`, with genuine site projections of `𝒬_h`; it satisfies `RenewalBranch` and is
  physically stationary (zero test lifts).

Clause (iii) depends on `thm:native-closure` and `cor:native-rate`, which are open in the
ledger; it is not formalised here.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace RenewalGeometry
namespace EinsteinSM

open RenewalRealization
open ShiftedJetAction (Grid unitVec)

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **The renewal branch** of `prop:renewal-interface`: every finite interface of the regulator
sequence is a renewal realization `renewalInterface n θ h_k hh` (lattice `(ℤ/n)⁴`, bank `θ`, the
regulator's cutoff `h_k`). -/
def RenewalBranch (reg : RegulatorSequence T FC) : Prop :=
  ∀ k, ∃ (m : ℕ) (hm : NeZero m) (θ : CoefficientBank (Fin 3)) (hh : 0 < reg.cutoff k),
    reg.iface k = @renewalInterface m hm θ (reg.cutoff k) hh

/-- **`cor:renewal-realization`, clause (i).**  On the renewal branch, the compactness
certificate, the coframe chart condition, first-variation consistency and the source bounds with
vanishing budget of `thm:main-limit` give, along every cutoff subsequence, a further subsequence
converging in the strong packet to a limit with physical bank that solves the classical
Einstein–Standard-Model equations distributionally. -/
theorem renewal_realization_limit (hT : 0 < T) (reg : RegulatorSequence T FC)
    (_hbranch : RenewalBranch reg)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      θ₀ ∈ physicalBanks ∧
      StrongPacket (fun k => reg.fields (ns (ψ k))) (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      FirstVariationsConverge FC reg.r0 (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ :=
  DiracStab.main_limit_closed hT reg hcert hch hcons hsrc hvan hyuk ns hns

/-- **`cor:renewal-realization`, clause (ii).**  On the renewal branch, the additional summable
transport hypothesis of `cor:cofinal-unique` gives convergence of the whole sequence to a unique
limit, independent of the route (any other regulator sequence with compact banks, the chart
condition and cofinally close fields has the same limit). -/
theorem renewal_realization_unique (hT : 0 < T) (reg : RegulatorSequence T FC)
    (_hbranch : RenewalBranch reg)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous)
    (htr : ∀ Q : ChartBox T, SummableTransport Q reg.fields reg.bank) :
    ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec), θ₀ ∈ physicalBanks ∧
      StrongPacket reg.fields reg.bank L θ₀ ∧
      FirstVariationsConverge FC reg.r0 reg.fields reg.bank L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ ∧
      (∀ (L' : LimitFields FC.C) (θ₀' : CoefficientBank Ysec),
        StrongPacket reg.fields reg.bank L' θ₀' →
          (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀') ∧
      ∀ (reg' : RegulatorSequence T FC),
        (∀ Q : ChartBox T, CoframeChartCondition Q reg'.fields) →
        (∃ P, IsCompactBankSet P ∧ ∀ n, reg'.bank n ∈ P) →
        (∀ Q : ChartBox T, ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ m ≥ N, ∀ n ≥ N,
          dK Q (reg.fields m) (reg.bank m) (reg'.fields n) (reg'.bank n) ≤ ε) →
        ∀ (L' : LimitFields FC.C) (θ₀' : CoefficientBank Ysec),
          StrongPacket reg'.fields reg'.bank L' θ₀' →
            (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀' :=
  cofinal_unique hT reg hcert hch hcons hsrc hvan hyuk htr

/-! ### Non-vacuity: a regulator sequence on the renewal branch -/

section Regulator

variable {n : ℕ} [NeZero n]

/-- The projection of `𝒬_h` onto the degrees of freedom of one lattice site. -/
def siteProj (x : Grid n) : Config n →ₗ[ℝ] Config n where
  toFun q := WithLp.toLp 2 fun p => if p.1 = x then q p else 0
  map_add' q q' := by
    ext p
    simp only [PiLp.toLp_apply, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c q := by
    ext p
    simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem siteProj_apply (x : Grid n) (q : Config n) (p : Grid n × Coord) :
    siteProj x q p = if p.1 = x then q p else 0 := by
  simp [siteProj]

theorem siteProj_sum (q : Config n) : ∑ x, siteProj x q = q := by
  ext p
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [siteProj_apply]
  rw [Finset.sum_eq_single p.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem siteProj_idem (x : Grid n) (q : Config n) : siteProj x (siteProj x q) = siteProj x q := by
  ext p
  simp only [siteProj_apply]
  split_ifs <;> simp_all

theorem siteProj_orth (x y : Grid n) (q : Config n) (hxy : x ≠ y) :
    siteProj x (siteProj y q) = 0 := by
  ext p
  simp only [siteProj_apply, PiLp.zero_apply]
  split_ifs with h1 h2 <;> simp_all

theorem siteProj_eq_coord {x : Grid n} {q q' : Config n} (hq : siteProj x q = siteProj x q')
    (c : Coord) : q (x, c) = q' (x, c) := by
  have := congrArg (fun r : Config n => r (x, c)) hq
  simpa [siteProj_apply] using this

/-- The lattice site `x ∈ (ℤ/n)⁴` placed in `M = (0,T) × 𝕋³`: time `T (x₀ + ½)/n`, spatial
point `(x_i/n)_i`. -/
def latticePos (T : ℝ) (x : Grid n) : ℝ × UnitAddTorus (Fin 3) :=
  (T * (((x 0).val : ℝ) + 1 / 2) / n, fun i => (((x i.succ).val : ℝ) / n : ℝ))

/-- The cutoffs `1/(k+1)`. -/
theorem one_div_succ_pos (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) := by positivity

/-- **A regulator sequence on the renewal branch** (`def:regulator`): the renewal realizations
of `prop:renewal-interface` on `(ℤ/n)⁴` at the cutoffs `1/(k+1)` with bank `θ`, the origin of
the configuration chart, flat constant reconstructions, the site projections of `𝒬_h`, and zero
test lifts. -/
def renewalRegulator (T : ℝ) (θ : CoefficientBank (Fin 3)) (n : ℕ) [NeZero n] :
    RegulatorSequence T (trivialCarrier (Fin 3)) where
  r0 := 4
  four_le_r0 := le_rfl
  cutoff k := 1 / ((k : ℝ) + 1)
  cutoff_pos k := one_div_succ_pos k
  cutoff_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  iface k := renewalInterface n θ _ (one_div_succ_pos k)
  yukawaEquiv _ := Equiv.refl _
  config _ := (0 : Config n)
  recon _ _ := constFields T _ 0 (fun _ => smLie.zero_mem) 0
  gravity_differentiable k := differentiable_gravityActionR θ _ _
  matter_differentiable k := differentiable_matterActionR θ _ _
  sitePos _ x := latticePos T x
  siteComp _ x := siteProj x
  siteComp_sum _ q := siteProj_sum q
  siteComp_idem _ x q := siteProj_idem x q
  siteComp_orth _ x y q h := siteProj_orth x y q h
  coframe_local _ x q q' h := by
    show chartCoframe (prm q x) = chartCoframe (prm q' x)
    congr 1
    funext a b
    exact siteProj_eq_coord h (Coord.frame a b)
  higgs_local _ x q q' h := by
    show hig q x = hig q' x
    funext i
    simp only [hig, siteProj_eq_coord h]
  enlarge K := K.enlarge
  enlarge_sub K := K.subset_interior_enlarge
  lift _ _ := 0
  lift_support _ _ _ _ _ := map_zero _

/-- The renewal regulator lies on the renewal branch. -/
theorem renewalRegulator_branch (T : ℝ) (θ : CoefficientBank (Fin 3)) (n : ℕ) [NeZero n] :
    RenewalBranch (renewalRegulator T θ n) :=
  fun k => ⟨n, inferInstance, θ, one_div_succ_pos k, rfl⟩

/-- The renewal regulator is physically stationary (zero test lifts). -/
theorem renewalRegulator_stationary (T : ℝ) (θ : CoefficientBank (Fin 3)) (n : ℕ) [NeZero n] :
    (renewalRegulator T θ n).PhysicallyStationary := by
  intro K
  have : ∀ k, (renewalRegulator T θ n).stationarityDefect k K = 0 := by
    intro k
    simp only [RegulatorSequence.stationarityDefect]
    refine le_antisymm (iSup₂_le fun v _ => ?_) zero_le
    have h0 : (renewalRegulator T θ n).lift k K v = 0 := rfl
    rw [h0, map_zero, abs_zero, ENNReal.ofReal_zero]
  simp only [this]
  exact tendsto_const_nhds

end Regulator

end EinsteinSM
end RenewalGeometry
