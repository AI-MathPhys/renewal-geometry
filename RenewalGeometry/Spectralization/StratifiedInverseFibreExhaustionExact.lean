/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Algebra.EquivariantOrbitDecomposition
import RenewalGeometry.Topology.FiniteInverseSystemStableImage
import RenewalGeometry.Spectralization.JointGramClassificationExact

/-!
# Finite stratified and completed semifinite inverse-fibre exhaustion

Paper `predictive_spectral_geometry`, labels `thm:supp-finite-exhaustion`
(`eq:supp-finite-fibre`) and `thm:supp-semifinite-exhaustion` (`eq:supp-semifinite-fibre`).

## Finite exhaustion

A **fully reduced finite realization** of the completed target `𝖲♯` is rendered by its retained
data: a joint Gram point `K ∈ Corr_X` (`thm:supp-common-source`,
`JointGram.CorrelationSpectrahedron`) together with points of the five retained fibres
`𝒥_X × ℳ_X × 𝒫_X × 𝒞_X^cal × ℛ_X` (directed current, dynamic memory, auxiliary markings,
calibration, marked monodromy).  The gauge group `𝒢_X = Π_a U(E_a)` acts on `Corr_X` by block
congruence and on the five factors; two realizations are equivalent when they are
simultaneously gauge equivalent (`RealizationSpace` is the orbit space
`ℛeal_X^{♯,min}(𝖲)`).  The theorem `finite_stratified_exhaustion` is the stratified orbit
decomposition along the equivariant joint Gram map (`EquivariantOrbit.orbitDecomposition`):

`ℛeal_X^{♯,min}(𝖲) ≃ Σ_{[K] ∈ Corr_X/𝒢_X} (𝒥_X × ℳ_X × 𝒫_X × 𝒞_X^cal × ℛ_X) / Stab_{𝒢_X}(K)`,

where the stratum of a realization is the gauge orbit of its Gram point, gauge orbits are the
block-congruence orbits of `thm:supp-common-source` (`mem_orbit_iff_gaugeAct`) and the
stabilizer is its residual gauge group (`mem_stabilizer_iff_jointGram`).  The five factor
classifications the paper composes are the separate records `thm:supp-graph-realization`
(`𝒥_X`), `thm:supp-Naimark-realization` / `thm:supp-complete-rational-Krein` (`ℳ_X`) and
`thm:supp-marked-bundle` (`ℛ_X`); here the factors enter as `𝒢_X`-sets.

## Semifinite completion

A completed finite-stage system (`CompletedStageSystem`) is an `ℕ`-inverse system of stage
fibres `𝔉_n` (compact Hausdorff, continuous bonding maps — the "nonempty compact finite strata"
with bonding onto stable images) together with the completed realization set `ℛeal_∞`, its
stage coordinates, the cofinal separating family (joint injectivity of the stage coordinates:
trivial common kernel on the quotient by the finite-stage coordinates) and tightness (every
compatible thread is realized).  Then

* `completedEquivSections`: `ℛeal_∞^{♯,min}(𝖲) ≃ varprojlim_n 𝔉_n` (`eq:supp-semifinite-fibre`);
* `completedEquivStableSections`: the inverse limit is taken over the stable images;
* `nonempty_completed_iff_stableImage`: it is nonempty exactly when the stable-image system is
  nonempty (finite-intersection property, `InverseSystem.nonempty_sections_iff_stableImage`);
* `completedEquivStratifiedSections`: with the stage fibres identified with their stratified
  forms by `thm:supp-finite-exhaustion`, the completed fibre is the inverse limit of the
  stratified stabilizer quotients;
* `weightLimit_lowerSemicontinuous`: the compatible increasing stage weights have a unique
  monotone limit which is lower semicontinuous (the semifinite-weight clause in its
  monotone-convergence form).
-/

set_option linter.unusedSectionVars false

namespace RenewalGeometry.StratifiedInverseFibre

open MulAction JointGram EquivariantOrbit

/-! ### The gauge action on the correlation spectrahedron -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → Type}
  [∀ a, Fintype (n a)] [∀ a, DecidableEq (n a)]

/-- `Corr_X` as a type. -/
abbrev Corr (n : ι → Type) [∀ a, Fintype (n a)] [∀ a, DecidableEq (n a)] : Type :=
  ↥(CorrelationSpectrahedron (n := n))

/-- The gauge group acts on `Corr_X` by `g • K = D(g⁻¹)ᴴ K D(g⁻¹)`: the block congruence
`gaugeAct` of `thm:supp-common-source` is a right action, and composing with inversion makes
it a left action with the same orbits and stabilizers. -/
instance instMulActionGaugeGroupCorr : MulAction (GaugeGroup n) (Corr n) where
  smul g K := ⟨gaugeAct g⁻¹ K.1, gaugeAct_mem_corr K.2 g⁻¹⟩
  one_smul K := Subtype.ext (by
    show gaugeAct (1 : GaugeGroup n)⁻¹ K.1 = K.1
    rw [inv_one, gaugeAct_one])
  mul_smul g h K := Subtype.ext (by
    show gaugeAct (g * h)⁻¹ K.1 = gaugeAct g⁻¹ (gaugeAct h⁻¹ K.1)
    rw [mul_inv_rev, gaugeAct_mul])

theorem smul_corr_val (g : GaugeGroup n) (K : Corr n) :
    ((g • K : Corr n) : Matrix (Σ a, n a) (Σ a, n a) ℂ) = gaugeAct g⁻¹ K.1 := rfl

theorem gaugeAct_gaugeAct_inv (g : GaugeGroup n) (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) :
    gaugeAct g (gaugeAct g⁻¹ K) = K := by
  rw [← gaugeAct_mul, inv_mul_cancel, gaugeAct_one]

theorem gaugeAct_inv_gaugeAct (g : GaugeGroup n) (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) :
    gaugeAct g⁻¹ (gaugeAct g K) = K := by
  rw [← gaugeAct_mul, mul_inv_cancel, gaugeAct_one]

/-- Gauge orbits in `Corr_X` are the block-congruence orbits `{D(g)ᴴ K D(g)}` of
`thm:supp-common-source`. -/
theorem mem_orbit_iff_gaugeAct (K K' : Corr n) :
    K ∈ orbit (GaugeGroup n) K' ↔ ∃ g : GaugeGroup n, gaugeAct g K'.1 = K.1 := by
  rw [mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by rw [← hg, smul_corr_val]⟩
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, Subtype.ext (by rw [smul_corr_val, inv_inv, hg])⟩

/-- The stabilizer of a Gram point is its residual gauge group `Stab_{𝒢_X}(K)`. -/
theorem mem_stabilizer_iff_jointGram (K : Corr n) (g : GaugeGroup n) :
    g ∈ stabilizer (GaugeGroup n) K ↔ g ∈ JointGram.stabilizer K.1 := by
  rw [MulAction.mem_stabilizer_iff, JointGram.mem_stabilizer_iff]
  constructor
  · intro h
    have h' : gaugeAct g⁻¹ K.1 = K.1 := congrArg Subtype.val h
    rw [← h', gaugeAct_gaugeAct_inv, h']
  · intro h
    apply Subtype.ext
    rw [smul_corr_val, ← h, gaugeAct_inv_gaugeAct, h]

/-! ### Fully reduced realizations and the stratified exhaustion -/

/-- The retained data of a fully reduced finite realization: a joint Gram point and points of
the five retained fibres `𝒥_X, ℳ_X, 𝒫_X, 𝒞_X^cal, ℛ_X`. -/
abbrev FullyReducedRealization (n : ι → Type) [∀ a, Fintype (n a)] [∀ a, DecidableEq (n a)]
    (J M P C R : Type) : Type :=
  Corr n × J × M × P × C × R

/-- The product of the five retained fibres. -/
abbrev FactorProduct (J M P C R : Type) : Type := J × M × P × C × R

variable (J M P C R : Type) [MulAction (GaugeGroup n) J] [MulAction (GaugeGroup n) M]
  [MulAction (GaugeGroup n) P] [MulAction (GaugeGroup n) C] [MulAction (GaugeGroup n) R]

/-- `ℛeal_X^{♯,min}(𝖲)`: fully reduced realizations modulo simultaneous gauge equivalence. -/
abbrev RealizationSpace : Type :=
  orbitRel.Quotient (GaugeGroup n) (FullyReducedRealization n J M P C R)

/-- The joint Gram map `(K, j, m, p, c, r) ↦ K`, gauge equivariant. -/
def gramMap : EquivariantMap (GaugeGroup n) (FullyReducedRealization n J M P C R) (Corr n) :=
  ⟨Prod.fst, fun _ _ => rfl⟩

/-- The fibre of the Gram map over `K` is the product of the five factors, equivariantly for
the stabilizer of `K`. -/
def gramFibreEquiv (K : Corr n) :
    (gramMap (n := n) J M P C R).fibre K ≃ FactorProduct J M P C R where
  toFun x := x.1.2
  invFun f := ⟨(K, f), rfl⟩
  left_inv x := Subtype.ext (Prod.ext x.2.symm rfl)
  right_inv _ := rfl

theorem gramFibreEquiv_smul (K : Corr n) (g : stabilizer (GaugeGroup n) K)
    (x : (gramMap (n := n) J M P C R).fibre K) :
    gramFibreEquiv J M P C R K (g • x) = g • gramFibreEquiv J M P C R K x := rfl

/-- The stratified stabilizer quotient of `eq:supp-finite-fibre`:
`Σ_{[K] ∈ Corr_X/𝒢_X} (𝒥_X × ℳ_X × 𝒫_X × 𝒞_X^cal × ℛ_X) / Stab_{𝒢_X}(K)`. -/
abbrev StratifiedQuotient : Type :=
  Σ ω : orbitRel.Quotient (GaugeGroup n) (Corr n),
    orbitRel.Quotient (stabilizer (GaugeGroup n) ω.out) (FactorProduct J M P C R)

/-- **`thm:supp-finite-exhaustion`, `eq:supp-finite-fibre`** (the bijection). -/
noncomputable def stratifiedExhaustion :
    RealizationSpace (n := n) J M P C R ≃ StratifiedQuotient (n := n) J M P C R :=
  (gramMap J M P C R).orbitDecomposition.trans
    (Equiv.sigmaCongrRight fun ω => orbitRelQuotientCongr (gramFibreEquiv J M P C R ω.out)
      (gramFibreEquiv_smul J M P C R ω.out))

/-- The stratum of the class of a realization is the gauge orbit of its Gram point. -/
theorem stratifiedExhaustion_fst (x : FullyReducedRealization n J M P C R) :
    (stratifiedExhaustion (n := n) J M P C R ⟦x⟧).1 = ⟦x.1⟧ :=
  (gramMap J M P C R).orbitDecomposition_fst x

/-- **`thm:supp-finite-exhaustion` (Finite stratified inverse-fibre exhaustion).**  For a
completed fully reduced finite target, the set of fully reduced realizations modulo
simultaneous gauge equivalence is the stratified stabilizer quotient `eq:supp-finite-fibre`:
there is a bijection `ℛeal_X^{♯,min}(𝖲) ≃ ⊔_{[K]} (𝒥 × ℳ × 𝒫 × 𝒞 × ℛ)/Stab(K)` sending the
class of a realization into the stratum of the gauge orbit of its joint Gram point; the
strata are indexed by the block-congruence orbits `Corr_X/𝒢_X` of `thm:supp-common-source`
and the quotient on each stratum is by its residual gauge group `Stab_{𝒢_X}(K)`. -/
theorem finite_stratified_exhaustion :
    (∃ e : RealizationSpace (n := n) J M P C R ≃ StratifiedQuotient (n := n) J M P C R,
      ∀ x : FullyReducedRealization n J M P C R, (e ⟦x⟧).1 = ⟦x.1⟧) ∧
    (∀ K K' : Corr n, (⟦K⟧ : orbitRel.Quotient (GaugeGroup n) (Corr n)) = ⟦K'⟧ ↔
      ∃ g : GaugeGroup n, gaugeAct g K'.1 = K.1) ∧
    (∀ (K : Corr n) (g : GaugeGroup n),
      g ∈ stabilizer (GaugeGroup n) K ↔ g ∈ JointGram.stabilizer K.1) :=
  ⟨⟨stratifiedExhaustion (n := n) J M P C R, stratifiedExhaustion_fst (n := n) J M P C R⟩,
    fun K K' => by rw [Quotient.eq, ← mem_orbit_iff_gaugeAct]; exact orbitRel_apply,
    mem_stabilizer_iff_jointGram⟩

/-! ### The completed quasilocal/semifinite system -/

universe u

/-- A completed finite-stage system (`thm:supp-semifinite-exhaustion`): the stage fibres `𝔉_n`
(fully reduced finite fibres, compact Hausdorff strata) with continuous bonding maps, the
completed realization set `ℛeal_∞` with its stage coordinates, the cofinal separating family
(the stage coordinates separate points: no additional retained quasilocal direction) and
tightness (every compatible thread of finite-stage data is realized). -/
structure CompletedStageSystem extends InverseSystem.{u} where
  /-- Topologies on the stage fibres. -/
  [top : ∀ n, TopologicalSpace (fibre n)]
  /-- The strata are compact. -/
  [compact : ∀ n, CompactSpace (fibre n)]
  /-- The strata are Hausdorff. -/
  [t2 : ∀ n, T2Space (fibre n)]
  /-- The bonding maps are continuous. -/
  bond_continuous : ∀ n, Continuous (bond n)
  /-- The completed realization set. -/
  Completed : Type u
  /-- The stage coordinates. -/
  coordinate : ∀ n, Completed → fibre n
  /-- The stage coordinates are compatible with the bonding maps. -/
  coordinate_bond : ∀ n r, bond n (coordinate (n + 1) r) = coordinate n r
  /-- Separation: the cofinal family of stage coordinates has trivial common kernel. -/
  separating : ∀ r r', (∀ n, coordinate n r = coordinate n r') → r = r'
  /-- Tightness: every compatible thread is realized. -/
  tight : ∀ x : ∀ n, fibre n, (∀ n, bond n (x (n + 1)) = x n) → ∃ r, ∀ n, coordinate n r = x n

namespace CompletedStageSystem

variable (S : CompletedStageSystem.{u})

attribute [instance] top compact t2

/-- The thread of stage coordinates of a completed realization. -/
def thread (r : S.Completed) : S.toInverseSystem.Sections :=
  ⟨fun n => S.coordinate n r, fun n => S.coordinate_bond n r⟩

theorem thread_injective : Function.Injective S.thread := fun r r' h =>
  S.separating r r' fun n => congrFun (congrArg Subtype.val h) n

theorem thread_surjective : Function.Surjective S.thread := fun x => by
  obtain ⟨r, hr⟩ := S.tight x.1 x.2
  exact ⟨r, Subtype.ext (funext hr)⟩

/-- **`eq:supp-semifinite-fibre`**: the completed fibre is the projective limit of the stage
fibres. -/
noncomputable def completedEquivSections : S.Completed ≃ S.toInverseSystem.Sections :=
  Equiv.ofBijective S.thread ⟨S.thread_injective, S.thread_surjective⟩

/-- The inverse limit is taken over the stable images. -/
noncomputable def completedEquivStableSections :
    S.Completed ≃ S.toInverseSystem.stableSystem.Sections :=
  S.completedEquivSections.trans S.toInverseSystem.sectionsEquivStable

/-- Every stage coordinate of a completed realization lies in the stable image. -/
theorem coordinate_mem_stableImage (r : S.Completed) (n : ℕ) :
    S.coordinate n r ∈ S.toInverseSystem.stableImage n :=
  S.toInverseSystem.mem_stableImage_of_sections (S.thread r) n

/-- The bonding maps map stable images onto stable images (Mittag-Leffler). -/
theorem bond_stableImage_surjective (n : ℕ) {e : S.fibre n}
    (he : e ∈ S.toInverseSystem.stableImage n) :
    ∃ y ∈ S.toInverseSystem.stableImage (n + 1), S.bond n y = e :=
  S.toInverseSystem.exists_mem_stableImage_bond_eq S.bond_continuous n he

/-- **Nonemptiness**: the completed fibre is nonempty exactly when the stable-image system is
nonempty (finite-intersection property of the compact strata). -/
theorem nonempty_completed_iff_stableImage :
    Nonempty S.Completed ↔ ∀ n, (S.toInverseSystem.stableImage n).Nonempty := by
  rw [S.completedEquivSections.nonempty_congr]
  exact S.toInverseSystem.nonempty_sections_iff_stableImage S.bond_continuous

/-- Equivalently, exactly when every stage fibre is nonempty. -/
theorem nonempty_completed_iff_fibre : Nonempty S.Completed ↔ ∀ n, Nonempty (S.fibre n) := by
  rw [S.completedEquivSections.nonempty_congr]
  exact S.toInverseSystem.nonempty_sections_iff_fibre S.bond_continuous

/-- **`eq:supp-semifinite-fibre`, stratified form**: identifying every stage fibre with its
stratified stabilizer quotient (`thm:supp-finite-exhaustion` at every stage, the bijections
`e n`), the completed fibre is the inverse limit of the stratified quotients, with the bonding
maps transported along the identifications. -/
noncomputable def completedEquivStratifiedSections (Strat : ℕ → Type u)
    (e : ∀ n, S.fibre n ≃ Strat n) :
    S.Completed ≃ (S.toInverseSystem.transport Strat e).Sections :=
  S.completedEquivSections.trans (S.toInverseSystem.sectionsEquivTransport Strat e)

end CompletedStageSystem

/-- **The semifinite-weight clause** (monotone convergence form): compatible increasing stage
weights `τ_n ≤ τ_{n+1}` on the completed data have the pointwise supremum `τ = ⨆_n τ_n` as
their unique monotone limit, which is lower semicontinuous when every `τ_n` is. -/
theorem weightLimit_lowerSemicontinuous {X : Type*} [TopologicalSpace X] (τ : ℕ → X → ENNReal)
    (hmono : ∀ n, τ n ≤ τ (n + 1)) (hlsc : ∀ n, LowerSemicontinuous (τ n)) :
    LowerSemicontinuous (fun x => ⨆ n, τ n x) ∧
    (∀ n x, τ n x ≤ ⨆ n, τ n x) ∧
    (∀ x, Filter.Tendsto (fun n => τ n x) Filter.atTop (nhds (⨆ n, τ n x))) := by
  refine ⟨lowerSemicontinuous_iSup hlsc, fun n x => le_iSup (fun n => τ n x) n, fun x => ?_⟩
  exact tendsto_atTop_iSup fun a b hab => (monotone_nat_of_le_succ fun n => hmono n) hab x

end RenewalGeometry.StratifiedInverseFibre
