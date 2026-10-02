/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Topology.FiniteInverseSystemPruning
import RenewalGeometry.Algebra.EquivariantOrbitDecomposition

/-!
# Compact finite-stage inverse systems

Paper `predictive_spectral_geometry`, `def:supp-compact-fibre-system` and
`lem:supp-fibre-pruning`.

* `CompactGroupQuotient`: a compact topological group acting continuously on a compact Hausdorff
  space acts properly, so the orbit space is compact Hausdorff
  (`compactSpace_orbitQuotient`, `t2Space_orbitQuotient`).
* `RestrictionSystem`: stages `F_n` with restriction maps `r_{m,n} : F_m → F_n` (`m ≥ n`),
  `r_{n,n} = id`, `r_{ℓ,n} = r_{m,n} r_{ℓ,m}`; `r_{n+k,n}` is the composite of the successive
  bonds (`r_eq_iterBond`), so the paper's stable images
  `F_n^∞ = ⋂_{m ≥ n} r_{m,n}(F_m)` are the stable images of the successive system
  (`stableImage_eq`), and compatible families for all `r_{m,n}` are the threads of the
  successive system (`sectionsEquiv`).
* `RestrictionSystem.fibre_pruning` (**`lem:supp-fibre-pruning`**) for compact Hausdorff stages
  with continuous restrictions.
* `CompactFiniteStageSystem` (**`def:supp-compact-fibre-system`**): increasing finite-rank
  screens `P_n ↑ I`; compact groups `𝒢_n` acting continuously on compact Hausdorff nonempty
  factor spaces `Corr_n, J̄_n, M̄_n, P̄_n, C̄_n^cal, R̄_n`; strata
  `F̄_n = (Corr_n × J̄_n × M̄_n × P̄_n × C̄_n^cal × R̄_n)/𝒢_n` (`Stratum`, compact Hausdorff
  nonempty); continuous restriction maps with the two composition laws; compatible
  self-adjoint stage resolvents `R_n(z)` on `P_n H` with a limiting resolvent family satisfying
  the resolvent identity, adjoint symmetry, injectivity and dense range; compatible finite-trace
  stage weights with their normal semifinite supremum; and compatible finite separating
  families on the retained completed data.
* `CompactFiniteStageSystem.orbitTypeDecomposition`: the orbit-type stratification
  `F̄_n ≃ Σ_{[K] ∈ Corr_n/𝒢_n} (J̄_n × M̄_n × P̄_n × C̄_n^cal × R̄_n)/Stab(K)` (a bijection,
  not a disjoint-union topology).
-/

set_option linter.unusedSectionVars false

open Filter Topology Set MulAction

noncomputable section

namespace RenewalGeometry.CompactFiniteStage

universe u

/-! ### Compact group quotients -/

section CompactGroupQuotient

variable {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MulAction G X] [TopologicalSpace X] [CompactSpace X] [T2Space X] [ContinuousSMul G X]

/-- A compact group acting continuously on a compact Hausdorff space acts properly. -/
theorem properSMul_of_compactSpace : ProperSMul G X :=
  ⟨(continuous_smul.prodMk continuous_snd).isProperMap⟩

/-- The orbit space of a compact group acting continuously on a compact Hausdorff space is
Hausdorff. -/
theorem t2Space_orbitQuotient : T2Space (orbitRel.Quotient G X) := by
  have := properSMul_of_compactSpace (G := G) (X := X)
  exact t2Space_quotient_mulAction_of_properSMul

/-- The orbit space of a compact space is compact. -/
theorem compactSpace_orbitQuotient : CompactSpace (orbitRel.Quotient G X) :=
  Quotient.compactSpace

end CompactGroupQuotient

/-! ### Restriction systems `r_{m,n}` -/

/-- An `ℕ`-indexed system with restriction maps `r_{m,n} : F_m → F_n` for `m ≥ n` satisfying
`r_{n,n} = id` and `r_{ℓ,n} = r_{m,n} ∘ r_{ℓ,m}`. -/
structure RestrictionSystem where
  /-- The stages. -/
  F : ℕ → Type u
  /-- The restriction maps. -/
  r : ∀ m n, n ≤ m → F m → F n
  r_self : ∀ n x, r n n le_rfl x = x
  r_trans : ∀ l m n (hnm : n ≤ m) (hml : m ≤ l) x, r l n (hnm.trans hml) x = r m n hnm (r l m hml x)

namespace RestrictionSystem

variable (R : RestrictionSystem.{u})

/-- The successive inverse system `r_{n+1,n}`. -/
abbrev toInverseSystem : InverseSystem.{u} where
  fibre := R.F
  bond n := R.r (n + 1) n (Nat.le_succ n)

/-- `r_{n+k,n}` is the composite of the successive bonds. -/
theorem r_eq_iterBond : ∀ (k n : ℕ) (x : R.F (n + k)),
    R.r (n + k) n (Nat.le_add_right n k) x = R.toInverseSystem.iterBond k n x
  | 0, n, x => R.r_self n x
  | k + 1, n, x => by
    show _ = R.toInverseSystem.iterBond k n (R.toInverseSystem.bond (n + k) x)
    rw [← r_eq_iterBond k n]
    exact R.r_trans (n + (k + 1)) (n + k) n (Nat.le_add_right n k) (Nat.le_succ _) x

/-- The paper's stable image `F_n^∞ = ⋂_{m ≥ n} r_{m,n}(F_m)`. -/
def stableImage (n : ℕ) : Set (R.F n) := ⋂ m, ⋂ (h : n ≤ m), range (R.r m n h)

theorem stableImage_eq (n : ℕ) : R.stableImage n = R.toInverseSystem.stableImage n := by
  rw [InverseSystem.stableImage_eq_iInter_range_iterBond]
  ext x
  rw [mem_iInter]
  unfold stableImage
  rw [mem_iInter₂]
  constructor
  · intro h k
    have := h (n + k) (Nat.le_add_right n k)
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by rw [← R.r_eq_iterBond]; exact hy⟩
  · intro h m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨y, hy⟩ := h k
    exact ⟨y, by rw [R.r_eq_iterBond]; exact hy⟩

/-- Compatible families for all restriction maps: the projective limit `lim_m F_m`. -/
def Sections : Type u := {x : ∀ n, R.F n // ∀ m n (h : n ≤ m), R.r m n h (x m) = x n}

/-- Compatible families for all `r_{m,n}` are exactly the threads of the successive system. -/
def sectionsEquiv : R.Sections ≃ R.toInverseSystem.Sections where
  toFun x := ⟨x.1, fun n => x.2 (n + 1) n (Nat.le_succ n)⟩
  invFun x := ⟨x.1, fun m n h => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have e0 := R.r_eq_iterBond k n (x.1 (n + k))
    refine Eq.trans e0 ?_
    clear h e0
    induction k with
    | zero => rfl
    | succ k ih =>
      have e : R.toInverseSystem.bond (n + k) (x.1 (n + k + 1)) = x.1 (n + k) := x.2 (n + k)
      show R.toInverseSystem.iterBond k n (R.toInverseSystem.bond (n + k) (x.1 (n + k + 1))) = _
      rw [e]
      exact ih⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`lem:supp-fibre-pruning` (Canonical pruning of compact finite-stage fibres).**  For
nonempty compact Hausdorff stages with continuous restriction maps, every stable image
`F_n^∞ = ⋂_{m ≥ n} r_{m,n}(F_m)` is nonempty and compact, `r_{n+1,n}(F_{n+1}^∞) = F_n^∞`,
`F_n^∞` is exactly the level-`n` projection of `lim_m F_m`, and it is the largest subsystem in
which every point extends (one step within the subsystem, hence indefinitely). -/
theorem fibre_pruning [∀ n, TopologicalSpace (R.F n)] [∀ n, CompactSpace (R.F n)]
    [∀ n, T2Space (R.F n)] (hcont : ∀ m n h, Continuous (R.r m n h))
    (hne : ∀ n, Nonempty (R.F n)) :
    (∀ n, (R.stableImage n).Nonempty ∧ IsCompact (R.stableImage n)) ∧
    (∀ n, R.r (n + 1) n (Nat.le_succ n) '' R.stableImage (n + 1) = R.stableImage n) ∧
    (∀ n, range (fun x : R.Sections => x.1 n) = R.stableImage n) ∧
    (∀ n, R.stableImage n ⊆ R.r (n + 1) n (Nat.le_succ n) '' R.stableImage (n + 1)) ∧
    (∀ T : ∀ n, Set (R.F n), (∀ n, T n ⊆ R.r (n + 1) n (Nat.le_succ n) '' T (n + 1)) →
      ∀ n, T n ⊆ R.stableImage n) := by
  have hc : ∀ n, Continuous (R.toInverseSystem.bond n) := fun n => hcont _ _ _
  obtain ⟨_, h1, h2, h3, h4, h5⟩ := R.toInverseSystem.fibre_pruning hc hne
  simp only [stableImage_eq]
  refine ⟨h1, h2, fun n => ?_, h4, h5⟩
  rw [← h3 n]
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨R.sectionsEquiv x, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨R.sectionsEquiv.symm x, rfl⟩

end RestrictionSystem

/-! ### The compact finite-stage inverse system -/

/-- **`def:supp-compact-fibre-system` (Compact finite-stage inverse system).**  On a complex
Hilbert space `H`:
* increasing finite-rank (finite-trace) orthogonal screens `P_n ↑ I`;
* compact Hausdorff topological gauge groups `𝒢_n` acting continuously on nonempty compact Hausdorff
  factor spaces `Corr_n, J̄_n, M̄_n, P̄_n, C̄_n^cal, R̄_n` (correlation spectrahedron, closed
  current polytope, compactified memory, markings, calibration, monodromy carrier); the strata
  are the diagonal quotients `F̄_n = (Corr_n × J̄_n × M̄_n × P̄_n × C̄_n^cal × R̄_n)/𝒢_n`;
* continuous restriction maps `r_{m,n} : F̄_m → F̄_n` with `r_{n,n} = id`,
  `r_{ℓ,n} = r_{m,n} r_{ℓ,m}`;
* compatible self-adjoint resolvent data: stage resolvents `R_n(z)` (`Im z ≠ 0`) living on
  `P_n H`, with `R_n(z)* = R_n(z̄)` and the resolvent identity, converging strongly to the
  transported limiting family `R(z)`, which satisfies the resolvent identity, adjoint symmetry,
  injectivity and dense range;
* compatible finite-trace stage weights (additive and positively homogeneous on positive
  operators, finite, increasing in `n`, retained on `P_n`) with the normal semifinite extension
  `τ = sup_n τ_n` (finite on every screen);
* the retained completed data with compatible stage coordinates and compatible finite families
  `𝓕_n` of separating functionals whose union has trivial common kernel after quotienting by
  the displayed coordinates. -/
structure CompactFiniteStageSystem (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
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
  resolvent : ℕ → ∀ z : ℂ, z.im ≠ 0 → H →L[ℂ] H
  resolvent_screen : ∀ n z hz,
    screen n * resolvent n z hz = resolvent n z hz ∧ resolvent n z hz * screen n = resolvent n z hz
  resolvent_adjoint : ∀ n z hz (hz' : ((starRingEnd ℂ) z).im ≠ 0),
    ContinuousLinearMap.adjoint (resolvent n z hz) = resolvent n ((starRingEnd ℂ) z) hz'
  resolvent_identity : ∀ n z w hz hw,
    resolvent n z hz - resolvent n w hw = (z - w) • (resolvent n z hz * resolvent n w hw)
  /-- The transported limiting resolvent family `R(z)`. -/
  limitResolvent : ∀ z : ℂ, z.im ≠ 0 → H →L[ℂ] H
  resolvent_tendsto : ∀ z hz x,
    Tendsto (fun n => resolvent n z hz x) atTop (𝓝 (limitResolvent z hz x))
  limit_identity : ∀ z w hz hw,
    limitResolvent z hz - limitResolvent w hw = (z - w) • (limitResolvent z hz * limitResolvent w hw)
  limit_adjoint : ∀ z hz (hz' : ((starRingEnd ℂ) z).im ≠ 0),
    ContinuousLinearMap.adjoint (limitResolvent z hz) = limitResolvent ((starRingEnd ℂ) z) hz'
  limit_injective : ∀ z hz, Function.Injective (limitResolvent z hz)
  limit_denseRange : ∀ z hz, DenseRange (limitResolvent z hz)
  /-- Compatible finite-trace stage weights `τ_n`. -/
  weight : ℕ → (H →L[ℂ] H) → ENNReal
  weight_add : ∀ n T U, T.IsPositive → U.IsPositive → weight n (T + U) = weight n T + weight n U
  weight_smul : ∀ n (c : NNReal) T, T.IsPositive → weight n ((c : ℂ) • T) = c * weight n T
  weight_finite : ∀ n T, T.IsPositive → weight n T < ⊤
  weight_screen : ∀ n T, weight n T = weight n (screen n * T * screen n)
  weight_mono : ∀ n T, T.IsPositive → weight n T ≤ weight (n + 1) T
  /-- The normal semifinite extension `τ = sup_n τ_n`. -/
  limitWeight : (H →L[ℂ] H) → ENNReal
  limitWeight_eq : ∀ T, T.IsPositive → limitWeight T = ⨆ n, weight n T
  limitWeight_semifinite : ∀ n, limitWeight (screen n) < ⊤
  /-- The retained completed data. -/
  Retained : Type u
  /-- The stage coordinates of the retained data. -/
  coordinate : ∀ n, Retained →
    orbitRel.Quotient (G n) (Corr n × Cur n × Mem n × Mark n × Cal n × Mon n)
  coordinate_restrict : ∀ m n h r, restrict m n h (coordinate m r) = coordinate n r
  /-- The compatible finite separating families `𝓕_n`. -/
  familySize : ℕ → ℕ
  family : ∀ n, Fin (familySize n) → Retained → ℂ
  /-- The cofinal family has trivial common kernel after quotienting by the displayed
  coordinates. -/
  separating : ∀ r r', (∀ n, coordinate n r = coordinate n r') →
    (∀ n i, family n i r = family n i r') → r = r'

namespace CompactFiniteStageSystem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : CompactFiniteStageSystem.{u} H)

attribute [instance] instGroup instTopG instTopGroup instCompactG instT2G instTopCorr instTopCur
  instTopMem instTopMark instTopCal instTopMon instCompactCorr instCompactCur instCompactMem
  instCompactMark instCompactCal instCompactMon instT2Corr instT2Cur instT2Mem instT2Mark
  instT2Cal instT2Mon instNonemptyCorr instNonemptyCur instNonemptyMem instNonemptyMark
  instNonemptyCal instNonemptyMon instActCorr instActCur instActMem instActMark instActCal
  instActMon instContCorr instContCur instContMem instContMark instContCal instContMon

/-- The product of the six factors at stage `n`. -/
abbrev Factors (n : ℕ) : Type u := S.Corr n × S.Cur n × S.Mem n × S.Mark n × S.Cal n × S.Mon n

/-- The fully reduced stratum `F̄_n = (Corr_n × J̄_n × M̄_n × P̄_n × C̄_n^cal × R̄_n)/𝒢_n`. -/
abbrev Stratum (n : ℕ) : Type u := orbitRel.Quotient (S.G n) (S.Factors n)

instance instCompactStratum (n : ℕ) : CompactSpace (S.Stratum n) := compactSpace_orbitQuotient

instance instT2Stratum (n : ℕ) : T2Space (S.Stratum n) := t2Space_orbitQuotient

instance instNonemptyStratum (n : ℕ) : Nonempty (S.Stratum n) :=
  ⟨Quotient.mk _ (Classical.arbitrary _)⟩

/-- The restriction system of the strata. -/
abbrev restrictionSystem : RestrictionSystem.{u} where
  F := S.Stratum
  r := S.restrict
  r_self := S.restrict_self
  r_trans := S.restrict_trans

/-- The paper's stable images `F̄_n^∞` (`eq:supp-stable-fibre-images`). -/
abbrev stableImage (n : ℕ) : Set (S.Stratum n) := S.restrictionSystem.stableImage n

/-- **`lem:supp-fibre-pruning`** for a compact finite-stage inverse system. -/
theorem fibre_pruning :
    (∀ n, (S.stableImage n).Nonempty ∧ IsCompact (S.stableImage n)) ∧
    (∀ n, S.restrict (n + 1) n (Nat.le_succ n) '' S.stableImage (n + 1) = S.stableImage n) ∧
    (∀ n, range (fun x : S.restrictionSystem.Sections => x.1 n) = S.stableImage n) ∧
    (∀ n, S.stableImage n ⊆ S.restrict (n + 1) n (Nat.le_succ n) '' S.stableImage (n + 1)) ∧
    (∀ T : ∀ n, Set (S.Stratum n), (∀ n, T n ⊆ S.restrict (n + 1) n (Nat.le_succ n) '' T (n + 1)) →
      ∀ n, T n ⊆ S.stableImage n) :=
  S.restrictionSystem.fibre_pruning (fun m n h => S.restrict_continuous m n h)
    (fun n => inferInstanceAs (Nonempty (S.Stratum n)))

/-! ### Orbit-type decomposition -/

open RenewalGeometry.EquivariantOrbit

/-- The equivariant projection `Factors_n → Corr_n`. -/
def corrMap (n : ℕ) : EquivariantMap (S.G n) (S.Factors n) (S.Corr n) :=
  ⟨Prod.fst, fun _ _ => rfl⟩

/-- The fibre of the projection over `K` is the product of the other five factors,
equivariantly for the stabilizer of `K`. -/
def corrFibreEquiv (n : ℕ) (K : S.Corr n) :
    (S.corrMap n).fibre K ≃ (S.Cur n × S.Mem n × S.Mark n × S.Cal n × S.Mon n) where
  toFun x := x.1.2
  invFun f := ⟨(K, f), rfl⟩
  left_inv x := Subtype.ext (Prod.ext x.2.symm rfl)
  right_inv _ := rfl

theorem corrFibreEquiv_smul (n : ℕ) (K : S.Corr n) (g : stabilizer (S.G n) K)
    (x : (S.corrMap n).fibre K) :
    S.corrFibreEquiv n K (g • x) = g • S.corrFibreEquiv n K x := rfl

/-- **The orbit-type decomposition** of `def:supp-compact-fibre-system`:
`F̄_n ≃ Σ_{[K] ∈ Corr_n/𝒢_n} (J̄_n × M̄_n × P̄_n × C̄_n^cal × R̄_n)/Stab(K)` (a bijection;
the stratification is not a disjoint-union topology). -/
def orbitTypeDecomposition (n : ℕ) :
    S.Stratum n ≃ Σ ω : orbitRel.Quotient (S.G n) (S.Corr n),
      orbitRel.Quotient (stabilizer (S.G n) ω.out)
        (S.Cur n × S.Mem n × S.Mark n × S.Cal n × S.Mon n) :=
  (S.corrMap n).orbitDecomposition.trans
    (Equiv.sigmaCongrRight fun ω => orbitRelQuotientCongr (S.corrFibreEquiv n ω.out)
      (S.corrFibreEquiv_smul n ω.out))

/-- The stratum of the class of `(K, j, m, p, c, ρ)` is the gauge orbit of `K`. -/
theorem orbitTypeDecomposition_fst (n : ℕ) (x : S.Factors n) :
    (S.orbitTypeDecomposition n (Quotient.mk _ x)).1 = Quotient.mk _ x.1 :=
  (S.corrMap n).orbitDecomposition_fst x

end CompactFiniteStageSystem

end RenewalGeometry.CompactFiniteStage
