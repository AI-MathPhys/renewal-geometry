/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.CompactFiniteStageCompletion
import RenewalGeometry.OperatorLimits.PseudoResolventSelfAdjoint
import RenewalGeometry.OperatorLimits.NormalWeightSupremum

/-!
# Realization of the completed retained-coordinate inverse fibre

Paper `predictive_spectral_geometry`, `def:supp-compact-fibre-system` and
`thm:supp-semifinite-exhaustion`.

`CompactFiniteStage.CompactFiniteStageSystem` (file `CompactFiniteStageCompletion`) takes the
limiting resolvent family, its properties, the semifinite extension weight and the retained
completed data as *fields*, and the boxed isomorphism `eq:supp-semifinite-fibre` there needs the
hypothesis `Tight` ("every compatible thread is realized").  This file removes both: it starts
from the **finite-stage input data** of `def:supp-compact-fibre-system`
(`CompactFiniteStageData`) and

* gives the retained completed inverse fibre a concrete meaning
  (`CompletedRealization`): a self-adjoint operator (resolvent presentation) whose resolvents
  are the strong limits of the stage resolvents, a normal weight that is the increasing limit of
  the stage weights, a compatible thread of fully reduced strata, and a possible additional
  retained quasilocal direction not displayed by any finite stage;
* **derives** all limiting fields (`toSystem`: the limit resolvent family by Banach–Steinhaus,
  its resolvent identity and adjoint symmetry by passing to the limit, dense range from
  injectivity, the semifinite normal extension as the supremum of the stage weights and its
  finiteness on every screen from compatibility);
* **proves** the realization step (`realize`, `tight`): every compatible thread is realized, using
  the pseudo-resolvent theorem (`IsSymmetricPseudoResolvent.toSelfAdjointResolventData`) for the
  operator and `NormalWeight.iSupWeight` for the weight;
* proves that the completed realization is determined by its thread (`eq_of_coords_eq`): the
  operator by uniqueness of the generator of a resolvent family, the weight by uniqueness of
  increasing limits, and the additional direction vanishes by the cofinal separation hypothesis
  (`extra_eq_zero`);
* concludes the boxed isomorphism `R_∞^{♯,min}(S) ≃ varprojlim_n F̄_n^∞`
  (`completedEquivStable`), its componentwise form on factor-preserving strata
  (`componentwiseCompletedEquiv`, with the realization of strata threads by threads of the six
  compact factors, `exists_factorThread`), and the full theorem
  (`semifinite_exhaustion_ofData`).

Rendering choices (disclosed): tightness of the memory factor is encoded, as in
`def:supp-compact-fibre-system`, by compactness of the compactified memory sets `M̄_n` (weak-*
compact tight sets with the point at infinity); normality of weights is the sequential form; the
separating families are linear functionals on the space `Q` of additional retained quasilocal
directions (after quotienting by the displayed coordinates), and a direction is *additional* when
no finite-stage functional displays it.
-/

set_option linter.unusedSectionVars false

open Filter Topology Set MulAction

noncomputable section

namespace RenewalGeometry.CompactFiniteStage

universe u

/-- **`def:supp-compact-fibre-system`, input data.**  On a complex Hilbert space `H`:
* increasing finite-rank orthogonal screens `P_n ↑ I`;
* compact Hausdorff gauge groups `𝒢_n` acting continuously on nonempty compact Hausdorff factor
  spaces `Corr_n, J̄_n, M̄_n, P̄_n, C̄_n^cal, R̄_n` (the compactified memory factor `M̄_n` being the
  weak-* compact tight memory set), with continuous restriction maps `r_{m,n}` between the strata
  `F̄_n = (Corr_n × J̄_n × M̄_n × P̄_n × C̄_n^cal × R̄_n)/𝒢_n` satisfying the composition laws;
* compatible self-adjoint stage resolvent data: symmetric pseudo-resolvents `R_n(z)` living on
  `P_n H` (resolvent identity and `R_n(z)† = R_n(z̄)`), converging strongly at every non-real `z`
  (transport), with injective limit;
* compatible finite-trace normal stage weights `τ_n` (supported on `P_n`, finite, compatible:
  `τ_m(P_n T P_n) = τ_n(T)` for `m ≥ n`, increasing on positive operators);
* compatible finite separating families `𝓕_n` of linear functionals on the space `Q` of additional
  retained quasilocal directions, whose cofinal union has trivial common kernel.
No limiting object is part of the data. -/
structure CompactFiniteStageData (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The finite-trace screens `P_n`. -/
  screen : ℕ → H →L[ℂ] H
  screen_isSymmetricProjection : ∀ n, (screen n : H →ₗ[ℂ] H).IsSymmetricProjection
  screen_finiteRank : ∀ n, FiniteDimensional ℂ (LinearMap.range (screen n : H →ₗ[ℂ] H))
  screen_mono : ∀ n, screen (n + 1) * screen n = screen n
  screen_tendsto : ∀ x, Tendsto (fun n => screen n x) atTop (𝓝 x)
  /-- The compact gauge groups `𝒢_n`. -/
  G : ℕ → Type u
  [instGroup : ∀ n, Group (G n)]
  [instTopG : ∀ n, TopologicalSpace (G n)]
  [instTopGroup : ∀ n, IsTopologicalGroup (G n)]
  [instCompactG : ∀ n, CompactSpace (G n)]
  [instT2G : ∀ n, T2Space (G n)]
  /-- The six factor spaces. -/
  Corr : ℕ → Type u
  Cur : ℕ → Type u
  Mem : ℕ → Type u
  Mark : ℕ → Type u
  Cal : ℕ → Type u
  Mon : ℕ → Type u
  [instTopCorr : ∀ n, TopologicalSpace (Corr n)]
  [instTopCur : ∀ n, TopologicalSpace (Cur n)]
  [instTopMem : ∀ n, TopologicalSpace (Mem n)]
  [instTopMark : ∀ n, TopologicalSpace (Mark n)]
  [instTopCal : ∀ n, TopologicalSpace (Cal n)]
  [instTopMon : ∀ n, TopologicalSpace (Mon n)]
  [instCompactCorr : ∀ n, CompactSpace (Corr n)]
  [instCompactCur : ∀ n, CompactSpace (Cur n)]
  [instCompactMem : ∀ n, CompactSpace (Mem n)]
  [instCompactMark : ∀ n, CompactSpace (Mark n)]
  [instCompactCal : ∀ n, CompactSpace (Cal n)]
  [instCompactMon : ∀ n, CompactSpace (Mon n)]
  [instT2Corr : ∀ n, T2Space (Corr n)]
  [instT2Cur : ∀ n, T2Space (Cur n)]
  [instT2Mem : ∀ n, T2Space (Mem n)]
  [instT2Mark : ∀ n, T2Space (Mark n)]
  [instT2Cal : ∀ n, T2Space (Cal n)]
  [instT2Mon : ∀ n, T2Space (Mon n)]
  [instNonemptyCorr : ∀ n, Nonempty (Corr n)]
  [instNonemptyCur : ∀ n, Nonempty (Cur n)]
  [instNonemptyMem : ∀ n, Nonempty (Mem n)]
  [instNonemptyMark : ∀ n, Nonempty (Mark n)]
  [instNonemptyCal : ∀ n, Nonempty (Cal n)]
  [instNonemptyMon : ∀ n, Nonempty (Mon n)]
  [instActCorr : ∀ n, MulAction (G n) (Corr n)]
  [instActCur : ∀ n, MulAction (G n) (Cur n)]
  [instActMem : ∀ n, MulAction (G n) (Mem n)]
  [instActMark : ∀ n, MulAction (G n) (Mark n)]
  [instActCal : ∀ n, MulAction (G n) (Cal n)]
  [instActMon : ∀ n, MulAction (G n) (Mon n)]
  [instContCorr : ∀ n, ContinuousSMul (G n) (Corr n)]
  [instContCur : ∀ n, ContinuousSMul (G n) (Cur n)]
  [instContMem : ∀ n, ContinuousSMul (G n) (Mem n)]
  [instContMark : ∀ n, ContinuousSMul (G n) (Mark n)]
  [instContCal : ∀ n, ContinuousSMul (G n) (Cal n)]
  [instContMon : ∀ n, ContinuousSMul (G n) (Mon n)]
  /-- The restriction maps `r_{m,n}` on the strata. -/
  restrict : ∀ m n, n ≤ m →
    orbitRel.Quotient (G m) (Corr m × Cur m × Mem m × Mark m × Cal m × Mon m) →
      orbitRel.Quotient (G n) (Corr n × Cur n × Mem n × Mark n × Cal n × Mon n)
  restrict_continuous : ∀ m n h, Continuous (restrict m n h)
  restrict_self : ∀ n x, restrict n n le_rfl x = x
  restrict_trans : ∀ l m n (hnm : n ≤ m) (hml : m ≤ l) x,
    restrict l n (hnm.trans hml) x = restrict m n hnm (restrict l m hml x)
  /-- Stage resolvent data `R_n(z)` on `P_n H`. -/
  resolvent : ℕ → ResolventFamily H
  resolvent_screen : ∀ n z hz,
    screen n * resolvent n z hz = resolvent n z hz ∧ resolvent n z hz * screen n = resolvent n z hz
  /-- Each stage family satisfies the resolvent identity and the adjoint symmetry. -/
  resolvent_pseudo : ∀ n, IsSymmetricPseudoResolvent (resolvent n)
  /-- Transport: the stage resolvents converge strongly. -/
  resolvent_converges : ∀ z (hz : z.im ≠ 0) x, ∃ y, Tendsto (fun n => resolvent n z hz x) atTop (𝓝 y)
  /-- Injectivity of the transported limiting family: no nonzero vector is sent to `0`. -/
  limit_injective : ∀ z (hz : z.im ≠ 0) x, Tendsto (fun n => resolvent n z hz x) atTop (𝓝 0) → x = 0
  /-- Compatible finite-trace normal stage weights `τ_n`. -/
  weight : ℕ → NormalWeight H
  weight_finite : ∀ n T, T.IsPositive → weight n T < ⊤
  weight_compatible : ∀ m n, n ≤ m → ∀ T, weight m (screen n * T * screen n) = weight n T
  weight_mono : ∀ n T, T.IsPositive → weight n T ≤ weight (n + 1) T
  /-- The additional retained quasilocal directions (after quotienting by the displayed
  coordinates). -/
  Q : Type u
  [instAddCommGroupQ : AddCommGroup Q]
  [instModuleQ : Module ℂ Q]
  /-- The compatible finite separating families `𝓕_n`. -/
  familySize : ℕ → ℕ
  family : ∀ n, Fin (familySize n) → Q →ₗ[ℂ] ℂ
  /-- Cofinal separation: the union of the families has trivial common kernel. -/
  family_separating : ∀ q, (∀ n i, family n i q = 0) → q = 0

namespace CompactFiniteStageData

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : CompactFiniteStageData.{u} H)

attribute [instance] instGroup instTopG instTopGroup instCompactG instT2G instTopCorr instTopCur
  instTopMem instTopMark instTopCal instTopMon instCompactCorr instCompactCur instCompactMem
  instCompactMark instCompactCal instCompactMon instT2Corr instT2Cur instT2Mem instT2Mark
  instT2Cal instT2Mon instNonemptyCorr instNonemptyCur instNonemptyMem instNonemptyMark
  instNonemptyCal instNonemptyMon instActCorr instActCur instActMem instActMark instActCal
  instActMon instContCorr instContCur instContMem instContMark instContCal instContMon
  instAddCommGroupQ instModuleQ

/-- The restriction system of the strata. -/
abbrev restrictionSystem : RestrictionSystem.{u} where
  F n := orbitRel.Quotient (D.G n) (D.Corr n × D.Cur n × D.Mem n × D.Mark n × D.Cal n × D.Mon n)
  r := D.restrict
  r_self := D.restrict_self
  r_trans := D.restrict_trans

/-! ### Derived limiting objects -/

/-- The transported limiting resolvent family (strong limit, bounded by Banach–Steinhaus). -/
def limitResolvent : ResolventFamily H := strongLimit D.resolvent D.resolvent_converges

theorem tendsto_limitResolvent (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    Tendsto (fun n => D.resolvent n z hz x) atTop (𝓝 (D.limitResolvent z hz x)) :=
  tendsto_strongLimit D.resolvent D.resolvent_converges z hz x

/-- The limiting family satisfies the resolvent identity and the adjoint symmetry. -/
theorem limitResolvent_pseudo : IsSymmetricPseudoResolvent D.limitResolvent :=
  isSymmetricPseudoResolvent_strongLimit D.resolvent D.resolvent_converges D.resolvent_pseudo

theorem limitResolvent_injective (z : ℂ) (hz : z.im ≠ 0) :
    Function.Injective (D.limitResolvent z hz) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply D.limit_injective z hz x
  simpa [hx] using D.tendsto_limitResolvent z hz x

/-- **The completed operator** (pseudo-resolvent theorem): the self-adjoint operator whose
resolvents are the strong limits of the stage resolvents. -/
def limitOperator : SelfAdjointResolventData H :=
  D.limitResolvent_pseudo.toSelfAdjointResolventData (D.limitResolvent_injective _ _)

theorem limitOperator_resolvent (z : ℂ) (hz : z.im ≠ 0) :
    D.limitOperator.resolvent z hz = D.limitResolvent z hz := rfl

/-- **The completed weight**: the supremum of the increasing stage weights. -/
def limitWeight : NormalWeight H := NormalWeight.iSupWeight D.weight D.weight_mono

theorem limitWeight_apply (T : H →L[ℂ] H) : D.limitWeight T = ⨆ n, D.weight n T := rfl

theorem screen_mul_self (n : ℕ) : D.screen n * D.screen n = D.screen n := by
  ext x
  have h := congrArg (fun f : H →ₗ[ℂ] H => f x) (D.screen_isSymmetricProjection n).isIdempotentElem.eq
  simpa using h

theorem screen_isPositive (n : ℕ) : (D.screen n).IsPositive :=
  (ContinuousLinearMap.isPositive_toLinearMap_iff _).1 (D.screen_isSymmetricProjection n).isPositive

/-- The stage weights are supported on the screens. -/
theorem weight_screen (n : ℕ) (T : H →L[ℂ] H) :
    D.weight n T = D.weight n (D.screen n * T * D.screen n) :=
  (D.weight_compatible n n le_rfl T).symm

/-- `τ_m(P_n) = τ_n(P_n)` for `m ≥ n`. -/
theorem weight_screen_of_le {m n : ℕ} (h : n ≤ m) : D.weight m (D.screen n) = D.weight n (D.screen n) := by
  have e : D.screen n * (1 : H →L[ℂ] H) * D.screen n = D.screen n := by
    rw [mul_one, D.screen_mul_self]
  rw [← e, D.weight_compatible m n h, D.weight_compatible n n le_rfl]

/-- **Semifiniteness**: the completed weight is finite on every screen. -/
theorem limitWeight_screen_lt_top (n : ℕ) : D.limitWeight (D.screen n) < ⊤ := by
  refine lt_of_le_of_lt (iSup_le fun m => ?_) (D.weight_finite n _ (D.screen_isPositive n))
  rcases le_total n m with h | h
  · exact (D.weight_screen_of_le h).le
  · exact NormalWeight.monotone_apply D.weight D.weight_mono (D.screen_isPositive n) h

theorem limitWeight_isSemifinite : D.limitWeight.IsSemifinite :=
  ⟨D.screen, D.screen_isSymmetricProjection, D.screen_mono, D.screen_tendsto,
    D.limitWeight_screen_lt_top⟩

/-! ### The retained completed inverse fibre -/

/-- **The retained completed inverse fibre `R_∞^{♯,min}(S)`**: a completed realization consists
of
* a self-adjoint operator (resolvent presentation) whose resolvents are the strong limits of the
  stage resolvents;
* a normal weight to which the stage weights increase;
* a compatible thread of fully reduced strata (`r_{m,n}(x_m) = x_n`);
* an additional retained quasilocal direction, not displayed by any finite-stage functional. -/
structure CompletedRealization where
  /-- The completed self-adjoint operator. -/
  op : SelfAdjointResolventData H
  op_tendsto : ∀ z hz x, Tendsto (fun n => D.resolvent n z hz x) atTop (𝓝 (op.resolvent z hz x))
  /-- The completed normal weight. -/
  weight : NormalWeight H
  weight_eq : ∀ T, weight T = ⨆ n, D.weight n T
  /-- The compatible thread of strata. -/
  coords : D.restrictionSystem.Sections
  /-- An additional retained quasilocal direction. -/
  extra : D.Q
  extra_undisplayed : ∀ n i, D.family n i extra = 0

namespace CompletedRealization

variable {D}

/-- **No additional retained quasilocal coordinate** (cofinal separation). -/
theorem extra_eq_zero (r : D.CompletedRealization) : r.extra = 0 :=
  D.family_separating _ r.extra_undisplayed

/-- The completed operator is the pseudo-resolvent generator of the limiting family. -/
theorem op_eq (r : D.CompletedRealization) : r.op = D.limitOperator :=
  r.op.ext_of_resolvent _ fun z hz => by
    ext x
    exact tendsto_nhds_unique (r.op_tendsto z hz x) (D.tendsto_limitResolvent z hz x)

/-- The completed weight is the supremum weight. -/
theorem weight_eq_limitWeight (r : D.CompletedRealization) : r.weight = D.limitWeight :=
  NormalWeight.ext r.weight_eq

/-- **A completed realization is determined by its thread of strata.** -/
theorem eq_of_coords_eq {r r' : D.CompletedRealization} (h : r.coords = r'.coords) : r = r' := by
  have hop : r.op = r'.op := by rw [r.op_eq, r'.op_eq]
  have hw : r.weight = r'.weight := by rw [r.weight_eq_limitWeight, r'.weight_eq_limitWeight]
  have he : r.extra = r'.extra := by rw [r.extra_eq_zero, r'.extra_eq_zero]
  cases r
  cases r'
  cases hop
  cases hw
  cases h
  cases he
  rfl

end CompletedRealization

/-- **The realization step**: every compatible thread of strata is realized by a completed
realization (operator by the pseudo-resolvent theorem, weight by the supremum). -/
def realize (x : D.restrictionSystem.Sections) : D.CompletedRealization where
  op := D.limitOperator
  op_tendsto := D.tendsto_limitResolvent
  weight := D.limitWeight
  weight_eq _ := rfl
  coords := x
  extra := 0
  extra_undisplayed _ _ := map_zero _

@[simp] theorem realize_coords (x : D.restrictionSystem.Sections) : (D.realize x).coords = x := rfl

/-! ### The derived compact finite-stage system -/

/-- The compact finite-stage system of the data, with every limiting field **derived** and the
retained completed data the concrete completed realizations. -/
def toSystem : CompactFiniteStageSystem.{u} H where
  screen := D.screen
  screen_isSymmetricProjection := D.screen_isSymmetricProjection
  screen_finiteRank := D.screen_finiteRank
  screen_mono := D.screen_mono
  screen_tendsto := D.screen_tendsto
  G := D.G
  Corr := D.Corr
  Cur := D.Cur
  Mem := D.Mem
  Mark := D.Mark
  Cal := D.Cal
  Mon := D.Mon
  restrict := D.restrict
  restrict_continuous := D.restrict_continuous
  restrict_self := D.restrict_self
  restrict_trans := D.restrict_trans
  resolvent := D.resolvent
  resolvent_screen := D.resolvent_screen
  resolvent_adjoint n z hz hz' := (D.resolvent_pseudo n).adjoint z hz hz'
  resolvent_identity n z w hz hw := (D.resolvent_pseudo n).identity z w hz hw
  limitResolvent := D.limitResolvent
  resolvent_tendsto := D.tendsto_limitResolvent
  limit_identity := D.limitResolvent_pseudo.identity
  limit_adjoint := D.limitResolvent_pseudo.adjoint
  limit_injective := D.limitResolvent_injective
  limit_denseRange z hz := D.limitOperator.denseRange_resolvent hz
  weight n T := D.weight n T
  weight_add n T U hT hU := (D.weight n).map_add hT hU
  weight_smul n c T hT := (D.weight n).map_smul c hT
  weight_finite := D.weight_finite
  weight_screen := D.weight_screen
  weight_mono := D.weight_mono
  limitWeight T := D.limitWeight T
  limitWeight_eq _ _ := rfl
  limitWeight_semifinite := D.limitWeight_screen_lt_top
  Retained := D.CompletedRealization
  coordinate n r := r.coords.1 n
  coordinate_restrict m n h r := r.coords.2 m n h
  familySize := D.familySize
  family n i r := D.family n i r.extra
  separating r r' hc _ := CompletedRealization.eq_of_coords_eq (Subtype.ext (funext hc))

/-- **Tightness is now a theorem**: every compatible thread of strata is realized. -/
theorem tight : D.toSystem.Tight := by
  intro x
  refine ⟨D.realize (D.restrictionSystem.sectionsEquiv.symm x), ?_⟩
  rfl

/-- The separating families are (trivially) finite-stage functionals of the displayed
coordinates, because they vanish on every completed realization. -/
theorem familiesFactor : D.toSystem.FamiliesFactor := fun n i =>
  ⟨fun _ => 0, fun r => r.extra_undisplayed n i⟩

/-- **`eq:supp-semifinite-fibre`** (boxed isomorphism), now derived from the data: the retained
completed inverse fibre is `varprojlim_n F̄_n^∞`. -/
def completedEquivStable : D.CompletedRealization ≃ D.toSystem.stableStageSystem.Sections :=
  D.toSystem.completedEquivStable D.tight D.familiesFactor

theorem completedEquivStable_apply (r : D.CompletedRealization) (n : ℕ) :
    D.toSystem.stablePoint (D.completedEquivStable r) n = r.coords.1 n := rfl

/-- On a factor-preserving stratum: the retained completed fibre is the quotient of the
componentwise limit of the six factors by the limit gauge group. -/
def componentwiseCompletedEquiv (T : CompactFiniteStageSystem.FactorPreservingTransport D.toSystem) :
    D.CompletedRealization ≃ orbitRel.Quotient T.equivariantSystem.limitGroup
      T.equivariantSystem.spaceSystem.Sections :=
  D.toSystem.componentwiseCompletedEquiv D.tight D.familiesFactor T

/-- **Realization of threads of factor data**: on a factor-preserving stratum every completed
realization comes from a compatible thread of the six compact factors (compactness of the
factors and gauge groups, in particular of the tight memory sets), and the thread is unique up to
the limit gauge group. -/
theorem exists_factorThread (T : CompactFiniteStageSystem.FactorPreservingTransport D.toSystem)
    (r : D.CompletedRealization) :
    ∃ y : T.equivariantSystem.spaceSystem.Sections,
      T.equivariantSystem.limitQuotientMap (Quotient.mk _ y) =
        T.stageSectionsEquiv (D.toSystem.thread r) := by
  obtain ⟨q, hq⟩ :=
    T.equivariantSystem.limitQuotientMap_surjective T.φ_continuous T.ρ_continuous
      (T.stageSectionsEquiv (D.toSystem.thread r))
  induction q using Quotient.inductionOn with
  | h y => exact ⟨y, hq⟩

/-- **`thm:supp-semifinite-exhaustion` from the finite-stage data.**  For the input data of
`def:supp-compact-fibre-system` (compatible symmetric stage resolvents converging strongly with
injective limit, compatible increasing finite-trace normal weights, compact strata, cofinal
separating families):
1. the retained completed inverse fibre is `varprojlim_n F̄_n^∞`, compatibly with the stage
   coordinates (`eq:supp-semifinite-fibre`), with no tightness assumption on threads;
2. the inverse limit is nonempty and compact;
3. no additional retained quasilocal coordinate: a completed realization is determined by its
   thread, and its additional direction vanishes;
4. the strict-rate physical part is the set of threads in the relative interiors;
5. the stage resolvents converge strongly to the resolvents of a unique self-adjoint operator,
   which is self-adjoint in Mathlib's sense;
6. the stage weights increase to a normal semifinite weight. -/
theorem semifinite_exhaustion_ofData
    (CurI : ∀ n, Set (D.Cur n)) (MemI : ∀ n, Set (D.Mem n))
    (MarkI : ∀ n, Set (D.Mark n)) (CalI : ∀ n, Set (D.Cal n)) (MonI : ∀ n, Set (D.Mon n)) :
    (∃ e : D.CompletedRealization ≃ D.toSystem.stableStageSystem.Sections,
      ∀ r n, D.toSystem.stablePoint (e r) n = r.coords.1 n) ∧
    Nonempty D.toSystem.stableStageSystem.Sections ∧
    CompactSpace D.toSystem.stableStageSystem.Sections ∧
    (∀ r r' : D.CompletedRealization, r.coords = r'.coords → r = r') ∧
    (∀ r : D.CompletedRealization, r.extra = 0) ∧
    Nonempty ({r : D.CompletedRealization // ∀ n,
        r.coords.1 n ∈ D.toSystem.physicalStratum CurI MemI MarkI CalI MonI n} ≃
      {x : D.toSystem.stableStageSystem.Sections // ∀ n,
        D.toSystem.stablePoint x n ∈ D.toSystem.physicalStratum CurI MemI MarkI CalI MonI n}) ∧
    (∃! A : SelfAdjointResolventData H,
      ∀ z hz x, Tendsto (fun n => D.resolvent n z hz x) atTop (𝓝 (A.resolvent z hz x))) ∧
    IsSelfAdjoint D.limitOperator.op ∧
    D.limitWeight.IsSemifinite ∧
    (∀ T : H →L[ℂ] H, T.IsPositive →
      Tendsto (fun n => D.weight n T) atTop (𝓝 (D.limitWeight T))) := by
  refine ⟨⟨D.completedEquivStable, D.completedEquivStable_apply⟩,
    D.toSystem.nonempty_stableSections, D.toSystem.compactSpace_stableSections,
    fun r r' h => CompletedRealization.eq_of_coords_eq h,
    CompletedRealization.extra_eq_zero,
    ⟨D.toSystem.physicalPartEquiv D.tight D.familiesFactor _⟩,
    existsUnique_strongResolventLimit D.resolvent D.resolvent_converges D.resolvent_pseudo
      (D.limit_injective _ _),
    D.limitOperator.isSelfAdjoint_op, D.limitWeight_isSemifinite,
    fun T hT => NormalWeight.tendsto_iSupWeight D.weight D.weight_mono hT⟩

end CompactFiniteStageData

/-! ### Non-vacuity -/

section Example

open ComplexConjugate

/-- The scalar resolvent `(a - z)⁻¹` of multiplication by the real number `a` on `ℂ`. -/
def scalarResolvent (a : ℝ) : ResolventFamily ℂ := fun z _ => ((a : ℂ) - z)⁻¹ • (1 : ℂ →L[ℂ] ℂ)

theorem ofReal_sub_ne_zero (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) : (a : ℂ) - z ≠ 0 := by
  intro h
  apply hz
  have := congrArg Complex.im h
  simpa using this.symm

theorem scalarResolvent_pseudo (a : ℝ) : IsSymmetricPseudoResolvent (scalarResolvent a) where
  identity z w hz hw := by
    have hz0 := ofReal_sub_ne_zero a hz
    have hw0 := ofReal_sub_ne_zero a hw
    ext
    simp only [scalarResolvent, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    field_simp
    ring
  adjoint z hz hz' := by
    simp only [scalarResolvent, map_smulₛₗ, ContinuousLinearMap.adjoint_one, map_inv₀, map_sub,
      Complex.conj_ofReal]

/-- The trivial action of `Unit` on a type. -/
abbrev unitTrivialAction (X : Type) : MulAction Unit X where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- **Non-vacuity of `CompactFiniteStageData`**: `H = ℂ`, the operator multiplication by `1`
(stage resolvents `(1 - z)⁻¹`), the vector weight at `1`, a two-point current factor `Bool` with
trivial gauge group (so the completed fibre has two points), and a one-dimensional space of
additional directions separated by the identity functional. -/
def exampleData : CompactFiniteStageData.{0} ℂ where
  screen _ := 1
  screen_isSymmetricProjection _ := ⟨by simp [IsIdempotentElem], LinearMap.IsSymmetric.id⟩
  screen_finiteRank _ := inferInstance
  screen_mono _ := by simp
  screen_tendsto x := by simpa using tendsto_const_nhds
  G _ := Unit
  Corr _ := Unit
  Cur _ := Bool
  Mem _ := Unit
  Mark _ := Unit
  Cal _ := Unit
  Mon _ := Unit
  instActCur _ := unitTrivialAction Bool
  instContCur _ := ⟨continuous_snd⟩
  restrict _ _ _ x := x
  restrict_continuous _ _ _ := continuous_id
  restrict_self _ _ := rfl
  restrict_trans _ _ _ _ _ _ := rfl
  resolvent _ := scalarResolvent 1
  resolvent_screen _ _ _ := ⟨one_mul _, mul_one _⟩
  resolvent_pseudo _ := scalarResolvent_pseudo 1
  resolvent_converges z hz x := ⟨_, tendsto_const_nhds⟩
  limit_injective z hz x h := by
    have h0 := tendsto_nhds_unique tendsto_const_nhds h
    have hne : (1 : ℂ) - z ≠ 0 := by simpa using ofReal_sub_ne_zero 1 hz
    have h1 : (1 : ℂ) - z = 0 ∨ x = 0 := by simpa [scalarResolvent] using h0
    exact h1.resolve_left hne
  weight _ := NormalWeight.vectorWeight 1
  weight_finite _ T _ := NormalWeight.vectorWeight_lt_top 1 T
  weight_compatible _ _ _ T := by simp
  weight_mono _ _ _ := le_rfl
  Q := ℂ
  familySize _ := 1
  family _ _ := LinearMap.id
  family_separating q h := h 0 0

/-- The hypotheses are jointly satisfiable with a non-zero operator and weight: the completed
operator of the example sends its resolvent to `(1 - z)⁻¹`, the completed weight of the
identity is `1`, and the retained completed fibre is nonempty. -/
example : exampleData.limitWeight 1 = 1 ∧ Nonempty exampleData.CompletedRealization := by
  refine ⟨?_, ⟨exampleData.realize (exampleData.restrictionSystem.sectionsEquiv.symm
    (Classical.choice (exampleData.toSystem.stageSystem.nonempty_sections_of_compact
      exampleData.toSystem.continuous_bond
      (fun n => inferInstanceAs (Nonempty (exampleData.toSystem.Stratum n))))))⟩⟩
  simp [CompactFiniteStageData.limitWeight_apply, exampleData, NormalWeight.vectorWeight_apply]

/-- The constant thread with current coordinate `b`. -/
def exampleThread (b : Bool) : exampleData.restrictionSystem.Sections :=
  ⟨fun _ => Quotient.mk _ ((), b, (), (), (), ()), fun _ _ _ => rfl⟩

/-- The completed fibre of the example has two distinct points. -/
example : exampleData.realize (exampleThread true) ≠ exampleData.realize (exampleThread false) := by
  intro h
  have h1 := congrArg (fun r => r.coords.1 0) h
  obtain ⟨g, hg⟩ := Quotient.exact h1
  have h2 := congrArg (fun p => p.2.1) hg
  have h3 : (false : Bool) = true := h2
  exact Bool.noConfusion h3

end Example

end RenewalGeometry.CompactFiniteStage
