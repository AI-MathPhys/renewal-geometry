/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMReducedClosure

/-!
# Finite compactness certificates produce the classical strong packet
  (`thm:certificate-packet`, Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMCompactnessCertificates.lean` (`M = (0,T) × 𝕋³` lifted to `ℝ⁴`,
trivialised bundles, compact charts rendered as chart boxes `Q`, `H¹(Q) = W^{1,2}(Q)` with weak
gradients as data).  The conclusion is the literal `StrongPacket` of `def:strong-packet`: one limit
`z = (e, A, H, Ψ, Ψ̄)` and one bank `θ` with the strong convergences on **every** chart box.

## Generic infrastructure

* `tendsto_of_forall_strictMono_subseq`: the subsequence principle (a sequence converges if every
  subsequence has a further subsequence converging to the same point);
* `exists_diagonal_subseq`: the diagonal argument for countably many subsequence-stable,
  tail-stable properties;
* rational chart boxes: `ChartBox.IsRat`, `countable_ratBoxes`, `exists_ratBox_enum`,
  `exists_ratBox_sub` (every point of `Q ∩ Q'` lies in a rational box inside `Q ∩ Q'`) and the
  gluing principle `ae_of_ratBoxes`;
* `LimitFields.at`, `LimitFields.patch`: pointwise bundles of the limit components and patching.

## Diagonal extraction on every chart box

`exists_reducedConvergence_allCharts`: if the reduced certificate holds on every chart box, every
subsequence has a further subsequence with one limit `L`, `θ₀` and reduced convergence on **every**
chart box (diagonal over the countably many rational boxes, patched limit, then every chart box by
the subsequence principle `ReducedConvergence.of_subseq` and uniqueness on rational sub-boxes).
This upgrades `exists_diagonal_reducedConvergence` (slab boxes only).

## The strong upgrade

* `coframe_Linfty_of_H1`: `L^∞`-precompact coframes converging in `H¹` converge in `L^∞`;
* `exists_coframeInv_bound`, `coframe_bound_of_chart`: values in a compact subset of the
  nondegenerate chart give the bound `sup_h (‖e_h‖_∞ + ‖e_h^{-1}‖_∞) < ∞`;
* `exists_bank_lower`: banks in a compact physical set are bounded away from zero;
* `h1Tendsto_of_weak`: weak `H¹` convergence plus subsequential strong `L²` compactness of the
  values and of the first jets gives strong `H¹` convergence; `jet_l2SubseqCompact` (screens),
  `H1Cauchy.strong` (`H¹`-Cauchy sequences);
* `SpinorStrongRoute`: the spinor hypothesis used by the upgrade, provided by route (C4a)
  (`SpinorScreenRoute.spinorStrongRoute`) or by `H¹`-Cauchy spinors
  (`SpinorH1Cauchy.spinorStrongRoute`), which is the conclusion of `prop:dirac-stability` on route
  (C4b);
* `CompactnessCertificate.toReduced`: (C1)–(C5) together with the coframe chart condition give
  (R1)–(R5);
* `StrongPacketOn.of_reduced`: reduced convergence + the certificate give the strong packet on the
  chart box (Higgs `L⁴` by `ReducedConvergence.higgs_strong`, i.e. `prop:covariant-higgs-endpoint`;
  the Orlicz clause of (C3) is therefore not needed for the conclusion).

## `thm:certificate-packet`

* `certificate_packet_of_spinorStrong` (core form);
* **`certificate_packet_screen`** — route (C4a) on every chart: unconditional;
* **`certificate_packet`** — the certificate as stated (route (C4a) or (C4b) on each chart), with the
  conclusion of `prop:dirac-stability` (`H¹`-Cauchy spinors on the subslab) taken as a hypothesis
  for the charts using route (C4b) (`prop:dirac-stability` is open).

**Coframe chart (disclosed).**  `def:strong-packet` requires the limiting coframe in the oriented,
time-oriented chart `coframeChart = {det e > 0, e⁰₀ > 0}` ("the limiting coframe is in the same
orientation and signature chart").  Item (C1) only gives `|det e_h| ≥ c`; neither the sign of the
determinant nor a time-orientation margin is preserved by `L^∞` limits from (C1) alone (constant
coframes with `e⁰₀ = 1/n`, `det = 1` converge to a coframe with `e⁰₀ = 0`).  The theorems therefore
assume `CoframeChartCondition`: the coframes take values a.e. in one fixed compact subset of the
oriented time-oriented nondegenerate chart — item (R1) of `def:reduced-certificate`, the paper's
"fixed local ... frame identifications" in which the coframes are "uniformly nondegenerate".

Non-vacuity: `flatRegulator_certificatePacket_hyps` (the flat regulator satisfies all hypotheses
of `certificate_packet_screen`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### The subsequence principle and diagonal extraction -/

section GenericSubseq

/-- **Subsequence principle**: if every subsequence has a further subsequence converging to `x`,
the sequence converges to `x`. -/
theorem tendsto_of_forall_strictMono_subseq {X : Type*} [TopologicalSpace X] {f : ℕ → X} {x : X}
    (h : ∀ s : ℕ → ℕ, StrictMono s → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f (s (φ k))) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  by_contra hf
  obtain ⟨U, hU, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hf
  obtain ⟨s, hs, hsU⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨φ, -, hφ⟩ := h s hs
  obtain ⟨k, hk⟩ := (hφ.eventually hU).exists
  exact hsU (φ k) hk

/-- **Diagonal extraction** for countably many properties `P m` of subsequences that can always be
achieved by further extraction, are stable under further extraction and are determined by tails:
there is one subsequence satisfying all of them. -/
theorem exists_diagonal_subseq (P : ℕ → (ℕ → ℕ) → Prop)
    (hex : ∀ m (s : ℕ → ℕ), StrictMono s → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P m (s ∘ ψ))
    (hcomp : ∀ m (s ψ : ℕ → ℕ), StrictMono ψ → P m s → P m (s ∘ ψ))
    (htail : ∀ m (s : ℕ → ℕ) (k : ℕ), StrictMono s → P m (fun j => s (j + k)) → P m s) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∀ m, P m D := by
  choose ψ hψ hP using hex
  let Φ : ℕ → {f : ℕ → ℕ // StrictMono f} := fun m => Nat.rec
    ⟨ψ 0 id strictMono_id, hψ 0 id strictMono_id⟩
    (fun m F => ⟨F.1 ∘ ψ (m + 1) F.1 F.2, F.2.comp (hψ _ _ _)⟩) m
  have hΦs : ∀ m, (Φ (m + 1)).1 = (Φ m).1 ∘ ψ (m + 1) (Φ m).1 (Φ m).2 := fun m => rfl
  have hPm : ∀ m, P m (Φ m).1 := by
    intro m
    cases m with
    | zero => exact hP 0 id strictMono_id
    | succ m => exact hP (m + 1) (Φ m).1 (Φ m).2
  set D : ℕ → ℕ := fun k => (Φ k).1 k with hD
  have hDs : StrictMono D := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    show (Φ k).1 k < (Φ (k + 1)).1 (k + 1)
    rw [hΦs k]
    exact (Φ k).2.lt_iff_lt.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self k)
      ((hψ (k + 1) (Φ k).1 (Φ k).2).id_le (k + 1)))
  have hrange : ∀ m k, m ≤ k → range (Φ k).1 ⊆ range (Φ m).1 := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih =>
      rw [hΦs k]
      exact (range_comp_subset_range _ _).trans ih
  refine ⟨D, hDs, fun m => ?_⟩
  obtain ⟨χ, hχ, hχD⟩ := exists_strictMono_of_range (Φ m).2 hDs m
    (fun k => hrange m (k + m) (by omega) ⟨k + m, rfl⟩)
  refine htail m D m hDs ?_
  have e : (fun j => D (j + m)) = (Φ m).1 ∘ χ := funext hχD
  rw [e]
  exact hcomp m (Φ m).1 χ hχ (hPm m)

end GenericSubseq

/-! ### Rational chart boxes -/

section RatBoxes

variable {T : ℝ}

/-- A chart box with rational corners. -/
def ChartBox.IsRat (Q : ChartBox T) : Prop :=
  ∀ i, Q.a i ∈ range ((↑) : ℚ → ℝ) ∧ Q.b i ∈ range ((↑) : ℚ → ℝ)

theorem ChartBox.ext_ab {Q Q' : ChartBox T} (ha : Q.a = Q'.a) (hb : Q.b = Q'.b) : Q = Q' := by
  cases Q; cases Q'; cases ha; cases hb; rfl

/-- There are countably many rational chart boxes. -/
theorem countable_ratBoxes : {Q : ChartBox T | Q.IsRat}.Countable := by
  have h1 : {f : E4 | ∀ i, f i ∈ range ((↑) : ℚ → ℝ)}.Countable :=
    countable_pi fun _ => countable_range _
  have ht : {p : E4 × E4 | ∀ i, p.1 i ∈ range ((↑) : ℚ → ℝ) ∧
      p.2 i ∈ range ((↑) : ℚ → ℝ)}.Countable := by
    refine (h1.prod h1).mono ?_
    intro p hp
    exact ⟨fun i => (hp i).1, fun i => (hp i).2⟩
  refine MapsTo.countable_of_injOn (f := fun Q : ChartBox T => (Q.a, Q.b)) (fun Q hQ => hQ) ?_ ht
  intro Q _ Q' _ h
  exact ChartBox.ext_ab (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Every point of `Q ∩ Q'` lies in a rational chart box contained in `Q ∩ Q'`. -/
theorem exists_ratBox_sub (Q Q' : ChartBox T) {x : E4} (hx : x ∈ Q.set) (hx' : x ∈ Q'.set) :
    ∃ R : ChartBox T, R.IsRat ∧ x ∈ R.set ∧ R.set ⊆ Q.set ∧ R.set ⊆ Q'.set := by
  have hxQ := SobolevOpen.mem_box.mp hx
  have hxQ' := SobolevOpen.mem_box.mp hx'
  have hlo : ∀ i, ∃ q : ℚ, max (Q.a i) (Q'.a i) < q ∧ (q : ℝ) < x i := fun i =>
    exists_rat_btwn (max_lt (hxQ i).1 (hxQ' i).1)
  have hhi : ∀ i, ∃ q : ℚ, x i < q ∧ (q : ℝ) < min (Q.b i) (Q'.b i) := fun i =>
    exists_rat_btwn (lt_min (hxQ i).2 (hxQ' i).2)
  choose qa hqa using hlo
  choose qb hqb using hhi
  have hsp : ∀ i : Fin 3, (qb i.succ : ℝ) - qa i.succ ≤ 1 := fun i => by
    have h1 := (hqb i.succ).2
    have h2 := (hqa i.succ).1
    have h3 := Q.spatial_le i
    have h4 := min_le_left (Q.b i.succ) (Q'.b i.succ)
    have h5 := le_max_left (Q.a i.succ) (Q'.a i.succ)
    linarith
  let R : ChartBox T :=
    { a := fun i => qa i
      b := fun i => qb i
      lt := fun i => (hqa i).2.trans (hqb i).1
      time_pos := Q.time_pos.trans ((le_max_left _ _).trans_lt (hqa 0).1)
      time_lt := ((hqb 0).2.trans_le (min_le_left _ _)).trans Q.time_lt
      spatial_le := hsp }
  have hR : ∀ y ∈ R.set, ∀ i, max (Q.a i) (Q'.a i) < y i ∧ y i < min (Q.b i) (Q'.b i) := by
    intro y hy i
    have hy' := (SobolevOpen.mem_box.mp hy) i
    exact ⟨(hqa i).1.trans hy'.1, hy'.2.trans (hqb i).2⟩
  refine ⟨R, fun i => ⟨⟨qa i, rfl⟩, ⟨qb i, rfl⟩⟩,
    SobolevOpen.mem_box.mpr fun i => ⟨(hqa i).2, (hqb i).1⟩, fun y hy => ?_, fun y hy => ?_⟩
  · exact SobolevOpen.mem_box.mpr fun i =>
      ⟨(le_max_left _ _).trans_lt (hR y hy i).1, (hR y hy i).2.trans_le (min_le_left _ _)⟩
  · exact SobolevOpen.mem_box.mpr fun i =>
      ⟨(le_max_right _ _).trans_lt (hR y hy i).1, (hR y hy i).2.trans_le (min_le_right _ _)⟩

/-- An enumeration of the rational chart boxes (`T > 0`). -/
theorem exists_ratBox_enum (hT : 0 < T) :
    ∃ R : ℕ → ChartBox T, (∀ m, (R m).IsRat) ∧ ∀ Q : ChartBox T, Q.IsRat → ∃ m, R m = Q := by
  have hne : {Q : ChartBox T | Q.IsRat}.Nonempty := by
    obtain ⟨q₀, hq₀, hq₀T⟩ := exists_rat_btwn hT
    obtain ⟨q₁, hq₁, hq₁T⟩ := exists_rat_btwn hq₀T
    refine ⟨slabChart (q₀ : ℝ) (q₁ : ℝ) hq₀ hq₁ hq₁T, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨⟨q₀, by simp [slabChart]⟩, ⟨q₁, by simp [slabChart]⟩⟩
    · exact ⟨⟨0, by simp [slabChart]⟩, ⟨1, by simp [slabChart]⟩⟩
  obtain ⟨R, hR⟩ := countable_ratBoxes.exists_eq_range hne
  refine ⟨R, fun m => ?_, fun Q hQ => ?_⟩
  · have : R m ∈ range R := ⟨m, rfl⟩
    rw [← hR] at this
    exact this
  · have : Q ∈ range R := by rw [← hR]; exact hQ
    exact this

/-- **Gluing over rational boxes**: a property holding a.e. on every enumerated rational box inside
`Q ∩ Q'` holds a.e. on `Q ∩ Q'`. -/
theorem ae_of_ratBoxes {Q Q' : ChartBox T} {P : E4 → Prop} (R : ℕ → ChartBox T)
    (hR : ∀ R' : ChartBox T, R'.IsRat → ∃ m, R m = R')
    (h : ∀ m, (R m).set ⊆ Q.set → (R m).set ⊆ Q'.set → ∀ᵐ x ∂(R m).μ, P x) :
    ∀ᵐ x, x ∈ Q.set → x ∈ Q'.set → P x := by
  have h' : ∀ m, ∀ᵐ x, (R m).set ⊆ Q.set → (R m).set ⊆ Q'.set → x ∈ (R m).set → P x := by
    intro m
    by_cases hs : (R m).set ⊆ Q.set ∧ (R m).set ⊆ Q'.set
    · filter_upwards [(ae_restrict_iff' (R m).isOpen.measurableSet).mp (h m hs.1 hs.2)] with
        x hx _ _ hxm
      exact hx hxm
    · exact Eventually.of_forall fun x h1 h2 _ => absurd ⟨h1, h2⟩ hs
  filter_upwards [ae_all_iff.mpr h'] with x hx hxQ hxQ'
  obtain ⟨R', hR'r, hxR', hR'Q, hR'Q'⟩ := exists_ratBox_sub Q Q' hxQ hxQ'
  obtain ⟨m, rfl⟩ := hR R' hR'r
  exact hx m hR'Q hR'Q' hxR'

end RatBoxes

/-! ### Pointwise bundles of limit fields and patching -/

section Patch

variable {T : ℝ} {C : Type} [Fintype C]

/-- All ten components of a limit-field tuple at a point. -/
def LimitFields.at (L : LimitFields C) (x : E4) :=
  (L.e x, L.de x, L.A x, L.F x, L.H x, L.K x, L.Ψ x, L.dΨ x, L.Ψb x, L.dΨb x)

theorem LimitFields.AEEqOn.ae_at {Q : ChartBox T} {L L' : LimitFields C}
    (h : LimitFields.AEEqOn Q L L') : ∀ᵐ x ∂Q.μ, L.at x = L'.at x := by
  filter_upwards [h.e, h.de, h.A, h.F, h.H, h.K, h.Ψ, h.dΨ, h.Ψb, h.dΨb] with
    x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [LimitFields.at, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem LimitFields.aeEqOn_of_ae_at {Q : ChartBox T} {L L' : LimitFields C}
    (h : ∀ᵐ x ∂Q.μ, L.at x = L'.at x) : LimitFields.AEEqOn Q L L' := by
  have hc : ∀ x, L.at x = L'.at x → L.e x = L'.e x ∧ L.de x = L'.de x ∧ L.A x = L'.A x ∧
      L.F x = L'.F x ∧ L.H x = L'.H x ∧ L.K x = L'.K x ∧ L.Ψ x = L'.Ψ x ∧ L.dΨ x = L'.dΨ x ∧
      L.Ψb x = L'.Ψb x ∧ L.dΨb x = L'.dΨb x := fun x hx => by
    simp only [LimitFields.at, Prod.mk.injEq] at hx
    exact hx
  exact ⟨h.mono fun x hx => (hc x hx).1, h.mono fun x hx => (hc x hx).2.1,
    h.mono fun x hx => (hc x hx).2.2.1, h.mono fun x hx => (hc x hx).2.2.2.1,
    h.mono fun x hx => (hc x hx).2.2.2.2.1, h.mono fun x hx => (hc x hx).2.2.2.2.2.1,
    h.mono fun x hx => (hc x hx).2.2.2.2.2.2.1, h.mono fun x hx => (hc x hx).2.2.2.2.2.2.2.1,
    h.mono fun x hx => (hc x hx).2.2.2.2.2.2.2.2.1, h.mono fun x hx => (hc x hx).2.2.2.2.2.2.2.2.2⟩

/-- Patching a family of limit-field tuples along an index function `k`. -/
def LimitFields.patch (Lm : ℕ → LimitFields C) (k : E4 → ℕ) : LimitFields C :=
  ⟨fun x => (Lm (k x)).e x, fun x => (Lm (k x)).de x, fun x => (Lm (k x)).A x,
    fun x => (Lm (k x)).F x, fun x => (Lm (k x)).H x, fun x => (Lm (k x)).K x,
    fun x => (Lm (k x)).Ψ x, fun x => (Lm (k x)).dΨ x, fun x => (Lm (k x)).Ψb x,
    fun x => (Lm (k x)).dΨb x⟩

theorem LimitFields.patch_at (Lm : ℕ → LimitFields C) (k : E4 → ℕ) (x : E4) :
    (LimitFields.patch Lm k).at x = (Lm (k x)).at x := rfl

end Patch

/-! ### Reduced convergence on every chart box -/

section AllCharts

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- **Subsequence principle for reduced convergence**: if every subsequence has a further
subsequence converging in the reduced topology on `Q` to the fixed limit `(L, θ₀)`, and the reduced
certificate holds on `Q`, the whole sequence converges. -/
theorem ReducedConvergence.of_subseq {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (hc : ReducedCertificate Q z θ)
    (h : ∀ s : ℕ → ℕ, StrictMono s → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ReducedConvergence Q (fun k => z (s (φ k))) (fun k => θ (s (φ k))) L θ₀) :
    ReducedConvergence Q z θ L θ₀ := by
  obtain ⟨φ₀, -, h₀⟩ := h id strictMono_id
  obtain ⟨Ke, hKe, -, hKL⟩ := h₀.coframe_chart
  obtain ⟨Ke', hKe', hKn'⟩ := hc.coframe_chart
  exact
    { coframe_chart := ⟨Ke ∪ Ke', hKe.union hKe', fun n => (hKn' n).mono fun x hx => Or.inr hx,
        hKL.mono fun x hx => Or.inl hx⟩
      coframe_mem := h₀.coframe_mem
      coframe_tendsto := tendsto_of_forall_strictMono_subseq fun s hs => by
        obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.coframe_tendsto⟩
      conn_lie := h₀.conn_lie
      conn_mem := h₀.conn_mem
      conn_tendsto := tendsto_of_forall_strictMono_subseq fun s hs => by
        obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.conn_tendsto⟩
      curv_mem := h₀.curv_mem
      curv_weak := h₀.curv_weak
      curv_tendsto := tendsto_of_forall_strictMono_subseq fun s hs => by
        obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.curv_tendsto⟩
      higgs_mem := h₀.higgs_mem
      higgs_tendsto := tendsto_of_forall_strictMono_subseq fun s hs => by
        obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.higgs_tendsto⟩
      covgrad_mem := h₀.covgrad_mem
      covgrad_weak := h₀.covgrad_weak
      covgrad_tendsto := tendsto_of_forall_strictMono_subseq fun s hs => by
        obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.covgrad_tendsto⟩
      spinor_weak := ⟨fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψ, h₀.spinor_weak.2.1,
        hc.spinor_bounded, fun χ hχ c => tendsto_of_forall_strictMono_subseq fun s hs => by
          obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.spinor_weak.2.2.2.1 χ hχ c⟩,
        fun χ hχ i c => tendsto_of_forall_strictMono_subseq fun s hs => by
          obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.spinor_weak.2.2.2.2 χ hχ i c⟩⟩
      cospinor_weak := ⟨fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψb,
        h₀.cospinor_weak.2.1, hc.cospinor_bounded,
        fun χ hχ c => tendsto_of_forall_strictMono_subseq fun s hs => by
          obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.cospinor_weak.2.2.2.1 χ hχ c⟩,
        fun χ hχ i c => tendsto_of_forall_strictMono_subseq fun s hs => by
          obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.cospinor_weak.2.2.2.2 χ hχ i c⟩⟩
      bank_compact := hc.bank_compact
      bank_tendsto := tendsto_of_forall_strictMono_subseq fun s hs => by
        obtain ⟨φ, hφ, hr⟩ := h s hs; exact ⟨φ, hφ, hr.bank_tendsto⟩ }

/-- **Diagonal extraction on every chart box.**  If the reduced certificate holds on every chart
box, every subsequence has a further subsequence and one limit `(L, θ₀)` with reduced convergence
on **every** chart box. -/
theorem exists_reducedConvergence_allCharts (hT : 0 < T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (hcert : ∀ Q : ChartBox T, ReducedCertificate Q z θ)
    (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
      ∀ Q : ChartBox T, ReducedConvergence Q (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k)))
        L θ₀ := by
  obtain ⟨R, -, hRall⟩ := exists_ratBox_enum hT
  set P : ℕ → (ℕ → ℕ) → Prop := fun m s => ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
    ReducedConvergence (R m) (fun k => z (ns (s k))) (fun k => θ (ns (s k))) L θ₀ with hPdef
  have hex : ∀ m (s : ℕ → ℕ), StrictMono s → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P m (s ∘ ψ) :=
    fun m s hs => by
      obtain ⟨ψ, hψ, L, θ₀, h⟩ := (hcert (R m)).exists_reducedConvergence (ns ∘ s) (hns.comp hs)
      exact ⟨ψ, hψ, L, θ₀, h⟩
  have hcomp : ∀ m (s ψ : ℕ → ℕ), StrictMono ψ → P m s → P m (s ∘ ψ) :=
    fun m s ψ hψ ⟨L, θ₀, h⟩ => ⟨L, θ₀, h.comp hψ.tendsto_atTop⟩
  have htail : ∀ m (s : ℕ → ℕ) (k : ℕ), StrictMono s → P m (fun j => s (j + k)) → P m s :=
    fun m s k hs ⟨L, θ₀, h⟩ => ⟨L, θ₀, ReducedConvergence.of_tail k h
      ((hcert (R m)).comp (hns.comp hs))⟩
  obtain ⟨D, hD, hPD⟩ := exists_diagonal_subseq P hex hcomp htail
  choose Lm θm hLm using hPD
  have hLm' : ∀ m, ReducedConvergence (R m) (fun k => z (ns (D k))) (fun k => θ (ns (D k)))
      (Lm m) (θm 0) := fun m => (hLm m).with_bank (hLm 0).bank_tendsto
  -- agreement on overlaps
  have hagree : ∀ j m, ∀ᵐ x, x ∈ (R j).set → x ∈ (R m).set → (Lm j).at x = (Lm m).at x :=
    fun j m => ae_of_ratBoxes R hRall fun r hrj hrm =>
      (((hLm' j).mono hrj).unique ((hLm' m).mono hrm)).ae_at
  -- the patched limit
  classical
  set kf : E4 → ℕ := fun x => if h : ∃ m, x ∈ (R m).set then Nat.find h else 0 with hkf
  have hk : ∀ m, ∀ x ∈ (R m).set, x ∈ (R (kf x)).set := by
    intro m x hx
    have hex' : ∃ m, x ∈ (R m).set := ⟨m, hx⟩
    simp only [hkf, hex']
    exact Nat.find_spec hex'
  set L := LimitFields.patch Lm kf with hL
  have hpatch : ∀ m, LimitFields.AEEqOn (R m) (Lm m) L := fun m => by
    refine LimitFields.aeEqOn_of_ae_at ?_
    filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr fun j => hagree j m),
      ae_restrict_mem (R m).isOpen.measurableSet] with x hx hxm
    rw [hL, LimitFields.patch_at]
    exact (hx (kf x) (hk m x hxm) hxm).symm
  have hRm : ∀ m, ReducedConvergence (R m) (fun k => z (ns (D k))) (fun k => θ (ns (D k))) L
      (θm 0) := fun m => (hLm' m).congr_ae (hpatch m)
  refine ⟨D, hD, L, θm 0, fun Q => ?_⟩
  refine ReducedConvergence.of_subseq ((hcert Q).comp (hns.comp hD)) fun s hs => ?_
  obtain ⟨φ, hφ, L', θ', h'⟩ :=
    (hcert Q).exists_reducedConvergence (ns ∘ D ∘ s) (hns.comp (hD.comp hs))
  refine ⟨φ, hφ, ?_⟩
  have hsφ : Tendsto (s ∘ φ) atTop atTop := (hs.comp hφ).tendsto_atTop
  have hbank : BankTendsto (fun k => θ (ns (D (s (φ k))))) (θm 0) :=
    (hRm 0).bank_tendsto.comp hsφ
  have hae : LimitFields.AEEqOn Q L' L := by
    refine LimitFields.aeEqOn_of_ae_at ?_
    have := ae_of_ratBoxes (Q := Q) (Q' := Q) (P := fun x => L'.at x = L.at x) R hRall
      fun m hmQ _ => ((h'.mono hmQ).unique ((hRm m).comp hsφ)).ae_at
    filter_upwards [ae_restrict_of_ae this, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
    exact hx hxQ hxQ
  exact (h'.congr_ae hae).with_bank hbank

end AllCharts

/-! ### Coframes: uniform convergence and inverse bounds -/

section CoframeUpgrade

variable {T : ℝ}

theorem norm_coframeC_eq (f : CoframeFibre) :
    ‖(fun p : Fin 4 × Fin 4 => ((f p.1 p.2 : ℝ) : ℂ))‖ = ‖f‖ := by
  refine (norm_curry_eq (fun a μ => ((f a μ : ℝ) : ℂ))).trans ?_
  exact norm_pi_congr fun a => norm_pi_congr fun μ => Complex.norm_real _

/-- **`L^∞`-precompact coframes converging in `H¹` converge in `L^∞`** (the `L^∞` subsequential
limits are identified with the `H¹` limit through convergence in measure). -/
theorem coframe_Linfty_of_H1 {Q : ChartBox T} {e : ℕ → E4 → CoframeFibre}
    {de : ℕ → E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} {e₀ : E4 → CoframeFibre}
    {de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} (hP : LpPrecompact ⊤ Q.μ e)
    (hmem : ∀ n, MemH1 Q (coframeC (e n)) (de n)) (hmem₀ : MemH1 Q (coframeC e₀) de₀)
    (hH1 : H1Tendsto Q (fun n => coframeC (e n)) de (coframeC e₀) de₀) :
    LpTendsto ⊤ Q.μ e e₀ := by
  have : Fact ((1 : ℝ≥0∞) ≤ ⊤) := ⟨le_top⟩
  have hm := coframe_tendstoInMeasure hmem hmem₀ hH1
  refine tendsto_of_forall_strictMono_subseq fun s hs => ?_
  obtain ⟨φ, hφ, u₀, hu₀, ht⟩ := hP.exists_subseq_tendsto s
  refine ⟨φ, hφ, ?_⟩
  have h1 : TendstoInMeasure Q.μ (fun k => e (s (φ k))) atTop u₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by simp) (fun k => (hP.1 _).1) hu₀.1 ht
  have h2 : TendstoInMeasure Q.μ (fun k => e (s (φ k))) atTop e₀ :=
    hm.comp (hs.comp hφ).tendsto_atTop
  exact LpTendsto.congr_lim ht (tendstoInMeasure_ae_unique h1 h2)

theorem continuousAt_coframeInv {e : CoframeFibre} (he : (Matrix.of e).det ≠ 0) :
    ContinuousAt coframeInv e := by
  have h1 : ContinuousAt Ring.inverse (Matrix.of e).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ he
  exact continuousAt_matrix_inv (Matrix.of e) h1

/-- **Inverse coframes are bounded on a compact subset of the nondegenerate chart.** -/
theorem exists_coframeInv_bound {Ke : Set CoframeFibre} (hKe : IsCompactCoframeSet Ke) :
    ∃ M : ℝ, ∀ e ∈ Ke, ‖coframeInv e‖ ≤ M :=
  hKe.1.exists_bound_of_continuousOn fun e he =>
    (continuousAt_coframeInv (hKe.2 he).1.ne').continuousWithinAt

theorem eLpNorm_top_le_of_ae_mem {F : Type*} [NormedAddCommGroup F] {μ : Measure E4}
    {f : E4 → F} {S : Set F} {M : ℝ} (hM : ∀ y ∈ S, ‖y‖ ≤ M) (h : ∀ᵐ x ∂μ, f x ∈ S) :
    eLpNorm f ⊤ μ ≤ ENNReal.ofReal M := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (h.mono fun x hx => hM _ hx)

/-- **The coframe bound of `eq:strong-geometry`** from values in a compact subset of the chart:
`sup_h (‖e_h‖_∞ + ‖e_h^{-1}‖_∞) < ∞`. -/
theorem coframe_bound_of_chart {Q : ChartBox T} {e : ℕ → E4 → CoframeFibre}
    {Ke : Set CoframeFibre} (hKe : IsCompactCoframeSet Ke) (hKn : ∀ n, ∀ᵐ x ∂Q.μ, e n x ∈ Ke) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n,
      eLpNorm (e n) ⊤ Q.μ + eLpNorm (fun x => coframeInv (e n x)) ⊤ Q.μ ≤ B := by
  obtain ⟨M₁, hM₁⟩ := hKe.1.exists_bound_of_continuousOn (f := id) continuousOn_id
  obtain ⟨M₂, hM₂⟩ := exists_coframeInv_bound hKe
  refine ⟨ENNReal.ofReal M₁ + ENNReal.ofReal M₂, by simp, fun n => add_le_add ?_ ?_⟩
  · exact eLpNorm_top_le_of_ae_mem (S := Ke) hM₁ (hKn n)
  · exact eLpNorm_top_le_of_ae_mem (S := coframeInv '' Ke)
      (fun y ⟨e', he', hy⟩ => hy ▸ hM₂ e' he') ((hKn n).mono fun x hx => mem_image_of_mem _ hx)

end CoframeUpgrade

/-! ### Coefficient banks bounded away from zero -/

section BankLower

variable {Ysec : Type} [Fintype Ysec]

/-- Banks in a compact subset of the physical region have `κ, g_j, λ_H` bounded away from zero
(`eq:strong-parameters`). -/
theorem exists_bank_lower {P : Set (CoefficientBank Ysec)} (hP : IsCompactBankSet P)
    {θ : ℕ → CoefficientBank Ysec} (hθ : ∀ n, θ n ∈ P) :
    ∃ c > (0 : ℝ), ∀ n, c ≤ (θ n).kappa ∧ c ≤ (θ n).g1 ∧ c ≤ (θ n).g2 ∧ c ≤ (θ n).g3 ∧
      c ≤ (θ n).lambdaH := by
  set f : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) → ℝ :=
    fun p => min (p.1 0) (min (p.1 2) (min (p.1 3) (min (p.1 4) (p.1 5)))) with hf
  have hfc : Continuous f := by
    simp only [hf]
    fun_prop
  obtain ⟨p₀, hp₀, hmin⟩ := hP.1.exists_isMinOn ⟨_, mem_image_of_mem _ (hθ 0)⟩ hfc.continuousOn
  obtain ⟨θ₁, hθ₁, rfl⟩ := hp₀
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP.2 hθ₁
  refine ⟨f (bankCoords θ₁), ?_, fun n => ?_⟩
  · simp only [hf, bankCoords, lt_min_iff]
    simp [h1, h2, h3, h4, h5]
  · have h : f (bankCoords θ₁) ≤ f (bankCoords (θ n)) :=
      isMinOn_iff.mp hmin _ (mem_image_of_mem bankCoords (hθ n))
    have e : f (bankCoords (θ n)) = min (θ n).kappa (min (θ n).g1 (min (θ n).g2
        (min (θ n).g3 (θ n).lambdaH))) := by simp [hf, bankCoords]
    rw [e] at h
    simp only [le_min_iff] at h
    exact h

end BankLower

/-! ### Spinors: strong `H¹` convergence from weak convergence and strong compactness -/

section SpinorUpgrade

variable {T : ℝ} {ι' : Type} [Fintype ι']

/-- **Subsequential strong `L²(Q)` compactness**: every subsequence has a further subsequence
converging strongly in `L²(Q)`. -/
def L2SubseqCompact (Q : ChartBox T) {F : Type*} [NormedAddCommGroup F] (u : ℕ → E4 → F) :
    Prop :=
  ∀ s : ℕ → ℕ, StrictMono s → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ : E4 → F, MemLp u₀ 2 Q.μ ∧
    LpTendsto 2 Q.μ (fun k => u (s (φ k))) u₀

theorem L2SubseqCompact.comp {Q : ChartBox T} {F : Type*} [NormedAddCommGroup F]
    {u : ℕ → E4 → F} (h : L2SubseqCompact Q u) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    L2SubseqCompact Q (fun k => u (ψ k)) := fun s hs => h (ψ ∘ s) (hψ.comp hs)

theorem LpPrecompact.l2SubseqCompact {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {Q : ChartBox T} {u : ℕ → E4 → F} (h : LpPrecompact 2 Q.μ u) : L2SubseqCompact Q u :=
  fun s _ => by
    have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    exact h.exists_subseq_tendsto s

/-- **Weak plus strong compactness gives strong convergence in `H¹(Q)`**: a weakly `H¹`-convergent
sequence whose values and gradients are subsequentially strongly compact in `L²(Q)` converges
strongly in `H¹(Q)` (every strong subsequential limit is identified with the weak limit by the test
pairings, and the subsequence principle applies). -/
theorem h1Tendsto_of_weak {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} {u₀ : E4 → ι' → ℂ} {g₀ : E4 → Fin 4 → ι' → ℂ}
    (hw : WeakH1Tendsto Q u g u₀ g₀) (hu : L2SubseqCompact Q u) (hg : L2SubseqCompact Q g) :
    H1Tendsto Q u g u₀ g₀ := by
  refine tendsto_of_forall_strictMono_subseq fun s hs => ?_
  obtain ⟨φ₁, hφ₁, v, hv, hvt⟩ := hu s hs
  obtain ⟨φ₂, hφ₂, G, hG, hGt⟩ := hg (s ∘ φ₁) (hs.comp hφ₁)
  have hσt : Tendsto (fun k => s (φ₁ (φ₂ k))) atTop atTop :=
    (hs.comp (hφ₁.comp hφ₂)).tendsto_atTop
  have hvt' : LpTendsto 2 Q.μ (fun k => u (s (φ₁ (φ₂ k)))) v := hvt.comp hφ₂.tendsto_atTop
  have hGt' : LpTendsto 2 Q.μ (fun k => g (s (φ₁ (φ₂ k)))) G := hGt
  have hvu : v =ᵐ[Q.μ] u₀ := ae_eq_of_comp fun c =>
    ae_eq_of_pairings Q (memLp_pi_iff.mp hv c) (hw.2.1 c).memLp fun χ hχ =>
      tendsto_nhds_unique
        (SobolevOpen.tendsto_integral_test_of_L2 Q.isOpen.measurableSet Q.volume_ne_top hχ
          (fun k => (hw.1 (s (φ₁ (φ₂ k))) c).memLp) (memLp_pi_iff.mp hv c)
          (tendsto_eLpNorm_apply hvt' c))
        ((hw.2.2.2.1 χ hχ c).comp hσt)
  have hGg : G =ᵐ[Q.μ] g₀ := by
    have hc : ∀ i c, (fun x => G x i c) =ᵐ[Q.μ] fun x => g₀ x i c := fun i c =>
      ae_eq_of_pairings Q (memLp_pi_iff.mp (memLp_pi_iff.mp hG i) c) ((hw.2.1 c).memLp_grad i)
        fun χ hχ => tendsto_nhds_unique
          (SobolevOpen.tendsto_integral_test_of_L2 Q.isOpen.measurableSet Q.volume_ne_top hχ
            (fun k => (hw.1 (s (φ₁ (φ₂ k))) c).memLp_grad i)
            (memLp_pi_iff.mp (memLp_pi_iff.mp hG i) c)
            (tendsto_eLpNorm_apply (u := fun k x => g (s (φ₁ (φ₂ k))) x i)
              (tendsto_eLpNorm_apply hGt' i) c))
          ((hw.2.2.2.2 χ hχ i c).comp hσt)
    have := ae_all_iff.mpr fun i => ae_all_iff.mpr (hc i)
    filter_upwards [this] with x hx
    exact funext fun i => funext fun c => hx i c
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, ?_⟩
  have h1 := LpTendsto.congr_lim hvt' hvu
  have h2 := LpTendsto.congr_lim hGt' hGg
  have := h1.add h2
  simpa [H1Tendsto, h1Norm] using this

/-- A first-jet packet with a common compact screen and an `L²` bound is subsequentially strongly
compact in `L²(Q)` (`lem:screen`). -/
theorem jet_l2SubseqCompact {Q : ChartBox T} {g : ℕ → E4 → Fin 4 → ι' → ℂ}
    (hS : HasCommonCompactScreen Q (fun n x (q : Fin 4 × ι') => g n x q.1 q.2))
    (hB : LpBounded 2 Q.μ g) : L2SubseqCompact Q g := by
  intro s hs
  have hPB : LpBounded 2 Q.μ (fun n x (q : Fin 4 × ι') => g n x q.1 q.2) := by
    obtain ⟨B, hBt, hBn⟩ := hB
    exact ⟨B, hBt, fun n => le_of_eq_of_le (eLpNorm_congr_norm_ae
      (Eventually.of_forall fun x => norm_curry_eq _)) (hBn n)⟩
  obtain ⟨ψ, hψ, P₀, hP₀, hPt⟩ := hS.exists_subseq_tendsto Q hPB s hs
  refine ⟨ψ, hψ, fun x i c => P₀ x (i, c), ?_, ?_⟩
  · exact memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun c => memLp_pi_iff.mp hP₀ (i, c)
  · refine hPt.congr fun k => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    exact norm_curry_eq (fun (i : Fin 4) (c : ι') => g (s (ψ k)) x i c - P₀ x (i, c))

/-- `H¹(Q)`-Cauchy sequences (the conclusion of `prop:dirac-stability` on a chart box). -/
def H1Cauchy (Q : ChartBox T) (u : ℕ → E4 → ι' → ℂ) (g : ℕ → E4 → Fin 4 → ι' → ℂ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ N, ∀ m ≥ N, ∀ n ≥ N, h1Norm Q (u m - u n) (g m - g n) ≤ ENNReal.ofReal ε

/-- A Cauchy sequence in `L^p` is precompact. -/
theorem lpPrecompact_of_cauchy {F : Type*} [NormedAddCommGroup F] {μ : Measure E4}
    {p : ℝ≥0∞} {u : ℕ → E4 → F} (hmem : ∀ n, MemLp (u n) p μ)
    (hc : ∀ ε > (0 : ℝ), ∃ N, ∀ m ≥ N, ∀ n ≥ N, eLpNorm (u m - u n) p μ ≤ ENNReal.ofReal ε) :
    LpPrecompact p μ u := by
  refine ⟨hmem, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
  refine ⟨Finset.range (N + 1), fun n => ?_⟩
  by_cases hn : n ≤ N
  · exact ⟨n, Finset.mem_range.mpr (by omega), by simp [hε]⟩
  · refine ⟨N, Finset.mem_range.mpr (by omega), (hN n (by omega) N le_rfl).trans_lt ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)

/-- A precompact sequence in `L^p` is bounded in `L^p`. -/
theorem LpPrecompact.lpBounded {F : Type*} [NormedAddCommGroup F] {μ : Measure E4}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : ℕ → E4 → F} (h : LpPrecompact p μ u) : LpBounded p μ u := by
  obtain ⟨hmem, hnet⟩ := h
  obtain ⟨s, hs⟩ := hnet 1 one_pos
  refine ⟨ENNReal.ofReal 1 + ∑ m ∈ s, eLpNorm (u m) p μ, ENNReal.add_ne_top.mpr
    ⟨ENNReal.ofReal_ne_top, ENNReal.sum_ne_top.mpr fun m _ => (hmem m).eLpNorm_ne_top⟩,
    fun n => ?_⟩
  obtain ⟨m, hm, hnm⟩ := hs n
  calc eLpNorm (u n) p μ = eLpNorm ((u n - u m) + u m) p μ := by rw [sub_add_cancel]
    _ ≤ eLpNorm (u n - u m) p μ + eLpNorm (u m) p μ :=
        eLpNorm_add_le ((hmem n).1.sub (hmem m).1) (hmem m).1 hp
    _ ≤ _ := add_le_add hnm.le
        (Finset.single_le_sum (f := fun m => eLpNorm (u m) p μ) (fun _ _ => zero_le) hm)

/-- **`H¹`-Cauchy sequences are bounded and subsequentially strongly compact** (values and
gradients). -/
theorem H1Cauchy.strong {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} (hmem : ∀ n, MemH1 Q (u n) (g n)) (h : H1Cauchy Q u g) :
    H1Bounded Q u g ∧ L2SubseqCompact Q u ∧ L2SubseqCompact Q g := by
  have hu : ∀ n, MemLp (u n) 2 Q.μ := fun n => memLp_pi_iff.mpr fun c => (hmem n c).memLp
  have hg : ∀ n, MemLp (g n) 2 Q.μ := fun n =>
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun c => (hmem n c).memLp_grad i
  have hPu : LpPrecompact 2 Q.μ u := lpPrecompact_of_cauchy hu fun ε hε => by
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun m hm n hn => le_self_add.trans (hN m hm n hn)⟩
  have hPg : LpPrecompact 2 Q.μ g := lpPrecompact_of_cauchy hg fun ε hε => by
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun m hm n hn => le_add_self.trans (hN m hm n hn)⟩
  obtain ⟨B₁, hB₁, hB₁n⟩ := hPu.lpBounded (by norm_num)
  obtain ⟨B₂, hB₂, hB₂n⟩ := hPg.lpBounded (by norm_num)
  exact ⟨⟨B₁ + B₂, ENNReal.add_ne_top.mpr ⟨hB₁, hB₂⟩, fun n => add_le_add (hB₁n n) (hB₂n n)⟩,
    hPu.l2SubseqCompact, hPg.l2SubseqCompact⟩

end SpinorUpgrade

/-! ### From the certificate to the strong packet -/

section Packet

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- **Coframe chart condition** (item (R1) of `def:reduced-certificate`): the coframes take values
a.e. in one fixed compact subset of the oriented, time-oriented, nondegenerate coframe chart. -/
def CoframeChartCondition (Q : ChartBox T) (z : ℕ → SmoothFields T left) : Prop :=
  ∃ Ke, IsCompactCoframeSet Ke ∧ ∀ n, ∀ᵐ x ∂Q.μ, (z n).z.e x ∈ Ke

/-- Strong `H¹` compactness data of a spinor sequence on `Q`: an `H¹(Q)` bound and subsequential
strong `L²(Q)` compactness of the values and of the first-jet packets. -/
def SpinorH1Data (Q : ChartBox T) (Ψ : ℕ → E4 → SpinorFibre C) : Prop :=
  H1Bounded Q (fun n => spinorC (Ψ n)) (fun n => spinorGrad (Ψ n)) ∧
    L2SubseqCompact Q (fun n => spinorC (Ψ n)) ∧ L2SubseqCompact Q (fun n => spinorGrad (Ψ n))

/-- The spinor hypothesis used by the strong upgrade: strong `H¹` compactness data for the spinors
and for the dual spinors. -/
def SpinorStrongRoute (Q : ChartBox T) (z : ℕ → SmoothFields T left) : Prop :=
  SpinorH1Data Q (fun n => (z n).z.Ψ) ∧ SpinorH1Data Q (fun n => (z n).z.Ψb)

/-- **The conclusion of `prop:dirac-stability` on a chart box**: the spinors and the dual spinors
are Cauchy in `H¹(Q)`. -/
def SpinorH1Cauchy (Q : ChartBox T) (z : ℕ → SmoothFields T left) : Prop :=
  H1Cauchy Q (fun n => spinorC (z n).z.Ψ) (fun n => spinorGrad (z n).z.Ψ) ∧
    H1Cauchy Q (fun n => spinorC (z n).z.Ψb) (fun n => spinorGrad (z n).z.Ψb)

theorem SpinorH1Data.comp {Q : ChartBox T} {Ψ : ℕ → E4 → SpinorFibre C} (h : SpinorH1Data Q Ψ)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) : SpinorH1Data Q (fun k => Ψ (ψ k)) :=
  ⟨h.1.comp ψ, h.2.1.comp hψ, h.2.2.comp hψ⟩

theorem SpinorStrongRoute.comp {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    (h : SpinorStrongRoute Q z) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    SpinorStrongRoute Q (fun k => z (ψ k)) :=
  ⟨h.1.comp hψ, h.2.comp hψ⟩

theorem spinorH1Data_of_screen {Q : ChartBox T} {Ψ : ℕ → E4 → SpinorFibre C}
    (hP : LpPrecompact 2 Q.μ (fun n => spinorC (Ψ n)))
    (hB : H1Bounded Q (fun n => spinorC (Ψ n)) (fun n => spinorGrad (Ψ n)))
    (hS : HasCommonCompactScreen Q (fun n => spinorJetPacket (Ψ n))) : SpinorH1Data Q Ψ :=
  ⟨hB, hP.l2SubseqCompact, jet_l2SubseqCompact hS hB.grad⟩

/-- **Route (C4a)** gives the strong spinor data. -/
theorem SpinorScreenRoute.spinorStrongRoute {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    (h : SpinorScreenRoute Q z) : SpinorStrongRoute Q z :=
  ⟨spinorH1Data_of_screen h.1 h.2.2.1 h.2.2.2.2.1,
    spinorH1Data_of_screen h.2.1 h.2.2.2.1 h.2.2.2.2.2⟩

/-- **`H¹`-Cauchy spinors** (the conclusion of `prop:dirac-stability`) give the strong spinor
data. -/
theorem SpinorH1Cauchy.spinorStrongRoute {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    (h : SpinorH1Cauchy Q z) : SpinorStrongRoute Q z :=
  ⟨H1Cauchy.strong (fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψ) h.1,
    H1Cauchy.strong (fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψb) h.2⟩

/-- **(C1)–(C5) with the coframe chart condition and the strong spinor data give (R1)–(R5).** -/
theorem CompactnessCertificate.toReduced {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (h : CompactnessCertificate Q z θ)
    (hch : CoframeChartCondition Q z) (hsp : SpinorStrongRoute Q z) : ReducedCertificate Q z θ where
  coframe_chart := hch
  coframe_bounded := h.coframe_bounded
  coframe_screen := h.coframe_screen
  conn_precompact := h.conn_precompact
  curv_bounded := h.curv_bounded
  curv_screen := h.curv_screen
  higgs_bounded := by
    obtain ⟨B, hB, hBn⟩ := h.higgs_bounded
    exact ⟨B, hB, fun n => le_self_add.trans (hBn n)⟩
  covgrad_bounded := h.covgrad_bounded
  covgrad_screen := h.covgrad_screen
  spinor_bounded := hsp.1.1
  cospinor_bounded := hsp.2.1
  bank_compact := h.bank_compact

/-- **Strong upgrade on one chart box**: reduced convergence, `L^∞` precompactness of the coframes
(C1) and the strong spinor data give the local convergences of `def:strong-packet`. -/
theorem StrongPacketOn.of_reduced {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (hRC : ReducedConvergence Q z θ L θ₀) (hP : LpPrecompact ⊤ Q.μ (fun n => (z n).z.e))
    (hsp : SpinorStrongRoute Q z) : StrongPacketOn Q z L := by
  obtain ⟨Ke, hKe, hKn, hKL⟩ := hRC.coframe_chart
  have hH := hRC.higgs_strong
  exact
    { coframe_Linfty := coframe_Linfty_of_H1 hP (fun n => memH1_coframe_of_smooth Q
        Q.isCompact_closure Q.closure_subset_cylSlab (z n).smooth_e) hRC.coframe_mem
        hRC.coframe_tendsto
      coframe_mem := hRC.coframe_mem
      coframe_H1 := hRC.coframe_tendsto
      coframe_bound := coframe_bound_of_chart hKe hKn
      limit_chart := hKL.mono fun x hx => hKe.2 hx
      conn_lie := hRC.conn_lie
      conn_mem := hRC.conn_mem
      conn_tendsto := hRC.conn_tendsto
      curv_mem := hRC.curv_mem
      curv_weak := hRC.curv_weak
      curv_tendsto := hRC.curv_tendsto
      higgs_mem := hH.2.2.1
      higgs_tendsto := hH.2.2.2
      covgrad_mem := hRC.covgrad_mem
      covgrad_weak := hRC.covgrad_weak
      covgrad_tendsto := hRC.covgrad_tendsto
      spinor_mem := hRC.spinor_weak.2.1
      spinor_tendsto := h1Tendsto_of_weak hRC.spinor_weak hsp.1.2.1 hsp.1.2.2
      cospinor_mem := hRC.cospinor_weak.2.1
      cospinor_tendsto := h1Tendsto_of_weak hRC.cospinor_weak hsp.2.2.1 hsp.2.2.2 }

/-- A fixed chart box `(T/3, 2T/3) × (0,1)³`. -/
def midChart (hT : 0 < T) : ChartBox T :=
  slabChart (T / 3) (2 * T / 3) (by positivity) (by linarith) (by linarith)

/-- **`thm:certificate-packet`, core form.**  If on every chart box the compactness certificate
holds, the coframes satisfy the chart condition and the spinors have strong `H¹` compactness data,
then every cutoff subsequence `ns` has a further subsequence `ns ∘ ψ` and limit fields
`z = L`, `θ₀` such that `z_{h_{ns(ψ k)}} → z` in the classical strong packet (`StrongPacket`:
every chart box) and, simultaneously, in the reduced topology on every chart box. -/
theorem certificate_packet_of_spinorStrong (hT : 0 < T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (hcert : ∀ Q : ChartBox T, CompactnessCertificate Q z θ)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q z)
    (hsp : ∀ Q : ChartBox T, SpinorStrongRoute Q z) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
      StrongPacket (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k))) L θ₀ ∧
      ∀ Q : ChartBox T, ReducedConvergence Q (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k)))
        L θ₀ := by
  obtain ⟨ψ, hψ, L, θ₀, hRC⟩ := exists_reducedConvergence_allCharts hT
    (fun Q => (hcert Q).toReduced (hch Q) (hsp Q)) ns hns
  have hs : StrictMono (ns ∘ ψ) := hns.comp hψ
  obtain ⟨P, hP, hθP⟩ := (hcert (midChart hT)).bank_compact
  obtain ⟨c, hc, hcθ⟩ := exists_bank_lower hP (fun k => hθP (ns (ψ k)))
  refine ⟨ψ, hψ, L, θ₀, ⟨fun Q => ?_, (hRC (midChart hT)).bank_tendsto, c, hc, hcθ⟩, hRC⟩
  exact StrongPacketOn.of_reduced (hRC Q) ((hcert Q).coframe_precompact.comp (ns ∘ ψ) le_top)
    ((hsp Q).comp hs)

/-- **`thm:certificate-packet`, route (C4a)** (unconditional).  A sequence of smooth reconstructed
fields satisfying the classical compactness certificate (C1)–(C5) with the spinor screen route
(C4a) on every chart box, and the coframe chart condition, has along every cutoff subsequence a
further subsequence and a field tuple `z = (e, A, H, Ψ, Ψ̄)`, `θ` for which all convergences of
`def:strong-packet` hold on every chart box; the limiting curvature is `F_A` and the limiting Higgs
derivative is `D_AH` (`HasWeakCurvature`, `HasWeakCovGrad`: not independent tensor limits). -/
theorem certificate_packet_screen (hT : 0 < T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (hcert : ∀ Q : ChartBox T, CompactnessCertificate Q z θ)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q z)
    (hroute : ∀ Q : ChartBox T, SpinorScreenRoute Q z) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
      StrongPacket (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k))) L θ₀ := by
  obtain ⟨ψ, hψ, L, θ₀, h, -⟩ := certificate_packet_of_spinorStrong hT hcert hch
    (fun Q => (hroute Q).spinorStrongRoute) ns hns
  exact ⟨ψ, hψ, L, θ₀, h⟩

/-- **`thm:certificate-packet`, the certificate as stated** (routes (C4a) or (C4b) on each chart
box), **conditional on `prop:dirac-stability` for route (C4b)**: on the chart boxes where only
the Lorentzian Dirac route (C4b) is available, the conclusion of `prop:dirac-stability` (spinors
and dual spinors Cauchy in `H¹` of the subslab, hence of the chart box) is taken as the hypothesis
`hdirac`. -/
theorem certificate_packet (hT : 0 < T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (hcert : ∀ Q : ChartBox T, CompactnessCertificate Q z θ)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q z)
    (hdirac : ∀ Q : ChartBox T, DiracStabilityRoute Q z → SpinorH1Cauchy Q z)
    (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
      StrongPacket (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k))) L θ₀ := by
  have hsp : ∀ Q : ChartBox T, SpinorStrongRoute Q z := fun Q =>
    (hcert Q).spinor_route.elim (fun h => h.spinorStrongRoute)
      (fun h => (hdirac Q h).spinorStrongRoute)
  obtain ⟨ψ, hψ, L, θ₀, h, -⟩ := certificate_packet_of_spinorStrong hT hcert hch hsp ns hns
  exact ⟨ψ, hψ, L, θ₀, h⟩

end Packet

/-! ### Non-vacuity -/

/-- The flat regulator satisfies the coframe chart condition on every chart box. -/
theorem flatRegulator_coframeChart (T : ℝ) (Q : ChartBox T) :
    CoframeChartCondition Q (flatRegulator T).fields :=
  ⟨{flatCoframe}, isCompactCoframeSet_flat, fun n => Eventually.of_forall fun x => rfl⟩

/-- The flat regulator satisfies the spinor screen route on every chart box. -/
theorem flatRegulator_spinorScreenRoute (T : ℝ) (Q : ChartBox T) :
    SpinorScreenRoute Q (flatRegulator T).fields := by
  have h := (flatRegulator_compactnessCertificate T Q).spinor_route
  rcases h with h | h
  · exact h
  · exact ⟨by simp only [flat_Ψ, spinorC_zero]; exact lpPrecompact_const MemLp.zero,
      by simp only [flat_Ψb, spinorC_zero]; exact lpPrecompact_const MemLp.zero,
      (flatRegulator_reducedCertificate T Q).spinor_bounded,
      (flatRegulator_reducedCertificate T Q).cospinor_bounded,
      by simp only [flat_Ψ, spinorJetPacket_zero]; exact hasCommonCompactScreen_zero Q,
      by simp only [flat_Ψb, spinorJetPacket_zero]; exact hasCommonCompactScreen_zero Q⟩

/-- **Non-vacuity of `certificate_packet_screen`**: the flat regulator satisfies every hypothesis
(and hence has a strong-packet subsequence). -/
theorem flatRegulator_certificatePacket_hyps {T : ℝ} (hT : 0 < T) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields Unit) (θ₀ : CoefficientBank Unit),
      StrongPacket (fun k => (flatRegulator T).fields (ψ k)) (fun k => (flatRegulator T).bank (ψ k))
        L θ₀ :=
  certificate_packet_screen hT (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) (flatRegulator_spinorScreenRoute T) id strictMono_id

end EinsteinSM
end RenewalGeometry
