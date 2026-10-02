/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.CompactFiniteStageSystem
import RenewalGeometry.Topology.InverseLimitOrbitQuotient

/-!
# The completed retained-coordinate inverse fibre

Paper `predictive_spectral_geometry`, `thm:supp-semifinite-exhaustion`, for the compact
finite-stage inverse systems of `def:supp-compact-fibre-system` (`CompactFiniteStageSystem`).

* `CompactFiniteStageSystem.completedEquivStable`: under tightness (every compatible thread of
  strata is realized by retained data) and cofinal separation (the separating families are
  finite-stage functionals of the displayed coordinates), the retained completed fibre is
  `varprojlim_n F̄_n^∞` (`eq:supp-semifinite-fibre`), compatibly with the stage coordinates;
* `coordinates_injective`: no additional retained quasilocal coordinate beyond the displayed
  finite-stage factors;
* `nonempty_stableSections`, `compactSpace_stableSections`: the inverse limit of the stable
  images is nonempty and compact (product topology);
* `physicalPartEquiv`: the strict-rate physical part (retained data whose coordinates lie in the
  images of the relative interiors of the compactified factors) corresponds exactly to the
  compatible threads lying in those interiors;
* `FactorPreservingTransport`, `componentwiseEquiv`: on a factor-preserving stratum (restriction
  maps induced by continuous equivariant factor maps over continuous group homomorphisms) the
  limit is written componentwise before the compact gauge quotient:
  `varprojlim F̄_n ≃ (varprojlim Corr_n × ... × varprojlim R̄_n)/(varprojlim 𝒢_n)`;
* `semifinite_exhaustion`: the packaged theorem (including the weight clause: the retained
  finite-trace weights increase to their normal semifinite extension).
-/

set_option linter.unusedSectionVars false

open Filter Topology Set MulAction

noncomputable section

namespace RenewalGeometry.CompactFiniteStage

universe u

namespace CompactFiniteStageSystem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : CompactFiniteStageSystem.{u} H)

/-- The successive inverse system of the strata. -/
abbrev stageSystem : InverseSystem.{u} := S.restrictionSystem.toInverseSystem

/-- The stable-image subsystem `n ↦ F̄_n^∞`. -/
abbrev stableStageSystem : InverseSystem.{u} := S.stageSystem.stableSystem

instance instTopStable (n : ℕ) : TopologicalSpace (S.stableStageSystem.fibre n) :=
  inferInstanceAs (TopologicalSpace (S.stageSystem.stableImage n))

/-- The level-`n` point (in `F̄_n`) of a stable thread. -/
def stablePoint (x : S.stableStageSystem.Sections) (n : ℕ) : S.Stratum n :=
  Subtype.val (p := fun y => y ∈ S.stageSystem.stableImage n) (x.1 n)

theorem continuous_bond (n : ℕ) : Continuous (S.stageSystem.bond n) :=
  S.restrict_continuous _ _ _

/-- The thread of stage coordinates of a retained datum. -/
def thread (r : S.Retained) : S.stageSystem.Sections :=
  ⟨fun n => S.coordinate n r, fun n => S.coordinate_restrict (n + 1) n (Nat.le_succ n) r⟩

/-- Tightness: every compatible thread of strata is realized by retained data. -/
def Tight : Prop := ∀ x : S.stageSystem.Sections, ∃ r, S.thread r = x

/-- The separating families are finite-stage functionals of the displayed coordinates. -/
def FamiliesFactor : Prop :=
  ∀ n i, ∃ f : S.Stratum n → ℂ, ∀ r, S.family n i r = f (S.coordinate n r)

/-- **No additional retained quasilocal coordinate**: the displayed stage coordinates determine
the retained datum. -/
theorem coordinates_injective (hfam : S.FamiliesFactor) : Function.Injective S.thread := by
  intro r r' h
  have hc : ∀ n, S.coordinate n r = S.coordinate n r' := fun n =>
    congrFun (congrArg Subtype.val h) n
  refine S.separating r r' hc fun n i => ?_
  obtain ⟨f, hf⟩ := hfam n i
  rw [hf, hf, hc]

/-- The retained completed fibre is the projective limit of the strata. -/
def completedEquivSections (htight : S.Tight) (hfam : S.FamiliesFactor) :
    S.Retained ≃ S.stageSystem.Sections :=
  Equiv.ofBijective S.thread ⟨S.coordinates_injective hfam, htight⟩

/-- **`eq:supp-semifinite-fibre`**: the retained completed fibre is `varprojlim_n F̄_n^∞`. -/
def completedEquivStable (htight : S.Tight) (hfam : S.FamiliesFactor) :
    S.Retained ≃ S.stableStageSystem.Sections :=
  (Equiv.ofBijective S.thread ⟨S.coordinates_injective hfam, htight⟩).trans
    S.stageSystem.sectionsEquivStable

theorem completedEquivStable_apply (htight : S.Tight) (hfam : S.FamiliesFactor)
    (r : S.Retained) (n : ℕ) :
    S.stablePoint (S.completedEquivStable htight hfam r) n = S.coordinate n r := rfl

/-- The inverse limit of the stable images is nonempty. -/
theorem nonempty_stableSections : Nonempty S.stableStageSystem.Sections := by
  have := S.stageSystem.nonempty_sections_of_compact S.continuous_bond
    (fun n => inferInstanceAs (Nonempty (S.Stratum n)))
  exact ⟨S.stageSystem.sectionsEquivStable (Classical.arbitrary _)⟩

/-- The inverse limit of the stable images is compact (product topology). -/
theorem compactSpace_stableSections : CompactSpace S.stableStageSystem.Sections := by
  have := S.stageSystem.compactSpace_sections S.continuous_bond
  exact S.stageSystem.sectionsHomeomorphStable.compactSpace

/-! ### The strict-rate physical part -/

/-- The image in the stratum of the product of the relative interiors of the compactified
factors (`Corr_n` is kept whole). -/
def physicalStratum (CurI : ∀ n, Set (S.Cur n)) (MemI : ∀ n, Set (S.Mem n))
    (MarkI : ∀ n, Set (S.Mark n)) (CalI : ∀ n, Set (S.Cal n)) (MonI : ∀ n, Set (S.Mon n))
    (n : ℕ) : Set (S.Stratum n) :=
  (fun x : S.Factors n => (Quotient.mk _ x : S.Stratum n)) ''
    (univ ×ˢ CurI n ×ˢ MemI n ×ˢ MarkI n ×ˢ CalI n ×ˢ MonI n)

/-- **Strict-rate physical part**: the retained data whose coordinates lie in the images of the
relative interiors correspond exactly to the compatible (stable) threads lying in those
interiors. -/
def physicalPartEquiv (htight : S.Tight) (hfam : S.FamiliesFactor) (Phys : ∀ n, Set (S.Stratum n)) :
    {r : S.Retained // ∀ n, S.coordinate n r ∈ Phys n} ≃
      {x : S.stableStageSystem.Sections // ∀ n, S.stablePoint x n ∈ Phys n} :=
  (S.completedEquivStable htight hfam).subtypeEquiv fun r => by
    simp only [completedEquivStable_apply]


/-! ### Componentwise form on factor-preserving strata -/

/-- Factor-preserving transport: the restriction maps `r_{n+1,n}` are induced by continuous
equivariant maps of each of the six factors over continuous homomorphisms
`φ_n : 𝒢_{n+1} → 𝒢_n`. -/
structure FactorPreservingTransport where
  /-- The gauge-group bonds. -/
  φ : ∀ n, S.G (n + 1) →* S.G n
  φ_continuous : ∀ n, Continuous (φ n)
  ρCorr : ∀ n, S.Corr (n + 1) → S.Corr n
  ρCur : ∀ n, S.Cur (n + 1) → S.Cur n
  ρMem : ∀ n, S.Mem (n + 1) → S.Mem n
  ρMark : ∀ n, S.Mark (n + 1) → S.Mark n
  ρCal : ∀ n, S.Cal (n + 1) → S.Cal n
  ρMon : ∀ n, S.Mon (n + 1) → S.Mon n
  ρCorr_continuous : ∀ n, Continuous (ρCorr n)
  ρCur_continuous : ∀ n, Continuous (ρCur n)
  ρMem_continuous : ∀ n, Continuous (ρMem n)
  ρMark_continuous : ∀ n, Continuous (ρMark n)
  ρCal_continuous : ∀ n, Continuous (ρCal n)
  ρMon_continuous : ∀ n, Continuous (ρMon n)
  ρCorr_smul : ∀ n (g : S.G (n + 1)) x, ρCorr n (g • x) = φ n g • ρCorr n x
  ρCur_smul : ∀ n (g : S.G (n + 1)) x, ρCur n (g • x) = φ n g • ρCur n x
  ρMem_smul : ∀ n (g : S.G (n + 1)) x, ρMem n (g • x) = φ n g • ρMem n x
  ρMark_smul : ∀ n (g : S.G (n + 1)) x, ρMark n (g • x) = φ n g • ρMark n x
  ρCal_smul : ∀ n (g : S.G (n + 1)) x, ρCal n (g • x) = φ n g • ρCal n x
  ρMon_smul : ∀ n (g : S.G (n + 1)) x, ρMon n (g • x) = φ n g • ρMon n x
  /-- The restriction maps are induced by the factor maps. -/
  restrict_mk : ∀ n (x : S.Factors (n + 1)),
    S.restrict (n + 1) n (Nat.le_succ n) (Quotient.mk _ x) =
      Quotient.mk _ (ρCorr n x.1, ρCur n x.2.1, ρMem n x.2.2.1, ρMark n x.2.2.2.1,
        ρCal n x.2.2.2.2.1, ρMon n x.2.2.2.2.2)

namespace FactorPreservingTransport

variable {S} (T : FactorPreservingTransport S)

/-- The product bond on the six factors. -/
def ρ (n : ℕ) : S.Factors (n + 1) → S.Factors n :=
  Prod.map (T.ρCorr n) (Prod.map (T.ρCur n) (Prod.map (T.ρMem n) (Prod.map (T.ρMark n)
    (Prod.map (T.ρCal n) (T.ρMon n)))))

theorem ρ_continuous (n : ℕ) : Continuous (T.ρ n) :=
  (T.ρCorr_continuous n).prodMap ((T.ρCur_continuous n).prodMap ((T.ρMem_continuous n).prodMap
    ((T.ρMark_continuous n).prodMap ((T.ρCal_continuous n).prodMap (T.ρMon_continuous n)))))

/-- The equivariant inverse system of the factor products. -/
def equivariantSystem : EquivariantInverseSystem.{u} where
  G := S.G
  X := S.Factors
  φ := T.φ
  ρ := T.ρ
  ρ_smul n g x := by
    obtain ⟨a, b, c, d, e, f⟩ := x
    simp only [ρ, Prod.map, Prod.smul_mk, T.ρCorr_smul, T.ρCur_smul, T.ρMem_smul, T.ρMark_smul,
      T.ρCal_smul, T.ρMon_smul]

instance instTopG' (n : ℕ) : TopologicalSpace (T.equivariantSystem.G n) :=
  inferInstanceAs (TopologicalSpace (S.G n))
instance instTopGroupG' (n : ℕ) : IsTopologicalGroup (T.equivariantSystem.G n) :=
  inferInstanceAs (IsTopologicalGroup (S.G n))
instance instCompactG' (n : ℕ) : CompactSpace (T.equivariantSystem.G n) :=
  inferInstanceAs (CompactSpace (S.G n))
instance instT2G' (n : ℕ) : T2Space (T.equivariantSystem.G n) :=
  inferInstanceAs (T2Space (S.G n))
instance instTopX' (n : ℕ) : TopologicalSpace (T.equivariantSystem.X n) :=
  inferInstanceAs (TopologicalSpace (S.Factors n))
instance instCompactX' (n : ℕ) : CompactSpace (T.equivariantSystem.X n) :=
  inferInstanceAs (CompactSpace (S.Factors n))
instance instT2X' (n : ℕ) : T2Space (T.equivariantSystem.X n) :=
  inferInstanceAs (T2Space (S.Factors n))
instance instContSMul' (n : ℕ) : ContinuousSMul (T.equivariantSystem.G n) (T.equivariantSystem.X n) :=
  inferInstanceAs (ContinuousSMul (S.G n) (S.Factors n))

/-- The factor inverse systems. -/
abbrev corrSystem : InverseSystem.{u} := ⟨S.Corr, T.ρCorr⟩
abbrev curSystem : InverseSystem.{u} := ⟨S.Cur, T.ρCur⟩
abbrev memSystem : InverseSystem.{u} := ⟨S.Mem, T.ρMem⟩
abbrev markSystem : InverseSystem.{u} := ⟨S.Mark, T.ρMark⟩
abbrev calSystem : InverseSystem.{u} := ⟨S.Cal, T.ρCal⟩
abbrev monSystem : InverseSystem.{u} := ⟨S.Mon, T.ρMon⟩

/-- **Componentwise limit before the gauge quotient**: the limit of the factor products is the
product of the six factor limits. -/
def factorSectionsEquiv :
    T.equivariantSystem.spaceSystem.Sections ≃
      T.corrSystem.Sections × T.curSystem.Sections × T.memSystem.Sections ×
        T.markSystem.Sections × T.calSystem.Sections × T.monSystem.Sections :=
  (InverseSystem.sectionsProdEquiv T.corrSystem
      (T.curSystem.prod (T.memSystem.prod (T.markSystem.prod (T.calSystem.prod T.monSystem))))).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((InverseSystem.sectionsProdEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
        ((InverseSystem.sectionsProdEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
          ((InverseSystem.sectionsProdEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
            (InverseSystem.sectionsProdEquiv _ _))))))))

/-- The limit of the strata is the limit of the orbit spaces of the factor products. -/
def stageSectionsEquiv :
    S.stageSystem.Sections ≃ T.equivariantSystem.quotientSystem.Sections :=
  S.stageSystem.sectionsEquivOfStageEquiv T.equivariantSystem.quotientSystem
    (fun n => Equiv.refl _) fun n y => by
      induction y using Quotient.inductionOn with
      | h x => exact T.restrict_mk n x

/-- **Componentwise form on a factor-preserving stratum**:
`varprojlim_n F̄_n ≃ (varprojlim_n (Corr_n × J̄_n × M̄_n × P̄_n × C̄_n^cal × R̄_n))/(varprojlim_n 𝒢_n)`,
where the limit of the products is the product of the six factor limits
(`factorSectionsEquiv`). -/
def componentwiseEquiv :
    S.stageSystem.Sections ≃
      orbitRel.Quotient T.equivariantSystem.limitGroup T.equivariantSystem.spaceSystem.Sections :=
  T.stageSectionsEquiv.trans
    (T.equivariantSystem.limitQuotientEquiv T.φ_continuous T.ρ_continuous).symm

end FactorPreservingTransport

/-! ### The packaged theorem -/

/-- **`thm:supp-semifinite-exhaustion` (Completed retained-coordinate inverse-fibre
theorem)**, for a compact finite-stage inverse system with tightness and finite-stage
separating families:
1. the retained completed fibre is `varprojlim_n F̄_n^∞`, compatibly with the stage
   coordinates (`eq:supp-semifinite-fibre`);
2. the inverse limit is nonempty and compact;
3. it contains no additional retained coordinate beyond the displayed finite-stage factors;
4. its strict-rate physical part is the set of compatible threads lying in the relative
   interiors of the compactified factors;
5. (the componentwise form on factor-preserving strata is `componentwise_form`);
6. the retained finite-trace weights increase to their normal semifinite extension. -/
theorem semifinite_exhaustion (htight : S.Tight) (hfam : S.FamiliesFactor)
    (CurI : ∀ n, Set (S.Cur n)) (MemI : ∀ n, Set (S.Mem n))
    (MarkI : ∀ n, Set (S.Mark n)) (CalI : ∀ n, Set (S.Cal n)) (MonI : ∀ n, Set (S.Mon n)) :
    (∃ e : S.Retained ≃ S.stableStageSystem.Sections,
      ∀ r n, S.stablePoint (e r) n = S.coordinate n r) ∧
    Nonempty S.stableStageSystem.Sections ∧ CompactSpace S.stableStageSystem.Sections ∧
    Function.Injective S.thread ∧
    Nonempty ({r : S.Retained // ∀ n,
        S.coordinate n r ∈ S.physicalStratum CurI MemI MarkI CalI MonI n} ≃
      {x : S.stableStageSystem.Sections // ∀ n,
        S.stablePoint x n ∈ S.physicalStratum CurI MemI MarkI CalI MonI n}) ∧
    (∀ T : H →L[ℂ] H, T.IsPositive →
      Tendsto (fun n => S.weight n T) atTop (𝓝 (S.limitWeight T)) ∧
      ∀ n, S.weight n T ≤ S.limitWeight T) := by
  refine ⟨⟨S.completedEquivStable htight hfam, S.completedEquivStable_apply htight hfam⟩,
    S.nonempty_stableSections, S.compactSpace_stableSections, S.coordinates_injective hfam,
    ⟨S.physicalPartEquiv htight hfam _⟩, fun T hT => ?_⟩
  rw [S.limitWeight_eq T hT]
  refine ⟨tendsto_atTop_iSup fun a b hab => ?_, fun n => le_iSup (fun n => S.weight n T) n⟩
  exact (monotone_nat_of_le_succ fun n => S.weight_mono n T hT) hab

/-- **Componentwise form** (`thm:supp-semifinite-exhaustion`, last clause): on a factor-preserving
stratum the retained completed fibre is the quotient of the componentwise limit by the limit
gauge group, and the componentwise limit is the product of the six factor limits. -/
def componentwiseCompletedEquiv (htight : S.Tight) (hfam : S.FamiliesFactor)
    (T : FactorPreservingTransport S) :
    S.Retained ≃ orbitRel.Quotient T.equivariantSystem.limitGroup
      T.equivariantSystem.spaceSystem.Sections :=
  (S.completedEquivSections htight hfam).trans T.componentwiseEquiv

end CompactFiniteStageSystem

/-! ### Non-vacuity -/

/-- The scalar resolvent `(0 - z)⁻¹` of the zero operator on `ℂ`. -/
noncomputable def trivialResolvent (z : ℂ) : ℂ →L[ℂ] ℂ := (-z)⁻¹ • (1 : ℂ →L[ℂ] ℂ)

theorem trivialResolvent_identity (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    trivialResolvent z - trivialResolvent w =
      (z - w) • (trivialResolvent z * trivialResolvent w) := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [h])
  have hw0 : w ≠ 0 := fun h => hw (by simp [h])
  ext
  simp [trivialResolvent]
  field_simp
  ring

theorem trivialResolvent_adjoint (z : ℂ) :
    ContinuousLinearMap.adjoint (trivialResolvent z) = trivialResolvent ((starRingEnd ℂ) z) := by
  rw [trivialResolvent, trivialResolvent, map_smulₛₗ, ContinuousLinearMap.adjoint_one]
  simp only [map_inv₀, map_neg]

/-- **Non-vacuity of `def:supp-compact-fibre-system`**: the trivial system on `H = ℂ` (identity
screens, trivial groups and one-point factors, resolvent of the zero operator, zero weights). -/
noncomputable def trivialSystem : CompactFiniteStageSystem.{0} ℂ where
  screen _ := 1
  screen_isSymmetricProjection _ := ⟨by simp [IsIdempotentElem], LinearMap.IsSymmetric.id⟩
  screen_finiteRank _ := inferInstance
  screen_mono _ := by simp
  screen_tendsto x := by simpa using tendsto_const_nhds
  G _ := Unit
  Corr _ := Unit
  Cur _ := Unit
  Mem _ := Unit
  Mark _ := Unit
  Cal _ := Unit
  Mon _ := Unit
  restrict _ _ _ _ := Quotient.mk _ ((), (), (), (), (), ())
  restrict_continuous _ _ _ := continuous_const
  restrict_self n x := by
    induction x using Quotient.inductionOn with
    | h a => rfl
  restrict_trans _ _ _ _ _ _ := rfl
  resolvent _ z _ := trivialResolvent z
  resolvent_screen _ _ _ := ⟨one_mul _, mul_one _⟩
  resolvent_adjoint _ z _ _ := trivialResolvent_adjoint z
  resolvent_identity _ z w hz hw := trivialResolvent_identity z w hz hw
  limitResolvent z _ := trivialResolvent z
  resolvent_tendsto _ _ _ := tendsto_const_nhds
  limit_identity z w hz hw := trivialResolvent_identity z w hz hw
  limit_adjoint z _ _ := trivialResolvent_adjoint z
  limit_injective z hz := by
    have hz0 : z ≠ 0 := fun h => hz (by simp [h])
    intro a b hab
    simpa [trivialResolvent, hz0] using hab
  limit_denseRange z hz := by
    have hz0 : z ≠ 0 := fun h => hz (by simp [h])
    refine Function.Surjective.denseRange fun y => ⟨-z * y, ?_⟩
    simp [trivialResolvent]
    field_simp
  weight _ _ := 0
  weight_add _ _ _ _ _ := by simp
  weight_smul _ _ _ _ := by simp
  weight_finite _ _ _ := ENNReal.zero_lt_top
  weight_screen _ _ := rfl
  weight_mono _ _ _ := le_rfl
  limitWeight _ := 0
  limitWeight_eq _ _ := by simp
  limitWeight_semifinite _ := ENNReal.zero_lt_top
  Retained := Unit
  coordinate _ _ := Quotient.mk _ ((), (), (), (), (), ())
  coordinate_restrict _ _ _ _ := rfl
  familySize _ := 0
  family _ i := Fin.elim0 i
  separating _ _ _ _ := rfl

/-- The trivial system is tight with finite-stage separating families, so the hypotheses of
`semifinite_exhaustion` are jointly satisfiable. -/
example : trivialSystem.Tight ∧ trivialSystem.FamiliesFactor := by
  refine ⟨fun x => ⟨(), ?_⟩, fun n i => Fin.elim0 i⟩
  apply Subtype.ext
  funext n
  exact Quotient.inductionOn (motive := fun q => _ = q) (x.1 n) fun a => rfl

end RenewalGeometry.CompactFiniteStage
