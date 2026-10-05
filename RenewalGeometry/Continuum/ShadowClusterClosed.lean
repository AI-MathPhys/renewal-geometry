/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CoupledBootstrapSlabModel
import RenewalGeometry.Continuum.AposterioriShadowRate
import RenewalGeometry.Action.NativeSelectedShadow

/-!
# The a posteriori shadow cluster with `prop:coupled-bootstrap` discharged

Einstein–Standard-Model action-closure manuscript, `thm:aposteriori-physical-shadow`,
`cor:shadow-harmonic-defect`, `cor:aposteriori-shadow-rate`, `thm:native-selected-shadow`.

The library theorems `AposterioriShadow.aposteriori_physical_shadow`,
`AposterioriShadow.shadow_harmonic_defect`, `AposterioriShadowRate.aposteriori_shadow_rate` and
`SelectedShadow.native_selected_shadow` are stated for an abstract slab model and carry the
conclusion of `prop:coupled-bootstrap` as the hypothesis `hboot`.  Here they are instantiated on
the concrete slab model `slabModel` of smooth actual field tuples on `ℝ × 𝕋³`, and `hboot` is
discharged by the proved `coupled_bootstrap`:

* `dBoot`, `CBoot` — the constants `d_*`, `C_*` of `prop:coupled-bootstrap` for the reference class
  `refSet` (compact chart margin `K`, `C_tH^{k+1}` bound `R₁`);
* `tube_bootstrap` — for every physical Cauchy tube (`ass:physical-Cauchy-tube`) whose exact
  solutions lie in `refSet` and whose declared constants are those of `prop:coupled-bootstrap`
  (`T.dstar ≤ d_*`, `C_* ≤ T.Cstar`), `CoupledBootstrapConclusion` holds on the tube family;
* `aposteriori_physical_shadow_closed`, `shadow_harmonic_defect_closed`,
  `aposteriori_shadow_rate_closed`, `native_selected_shadow_closed` — the four results without
  `hboot`.
-/

open Metric Filter Topology Asymptotics
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.CoupledBootstrap.ShadowClosed

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy QLDiff QLRecovery FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetCompleteForcing ActualJetState ActualJetRecon SpinorProlongation
  TwistedHalfRicci SlabSemi AposterioriShadow AposterioriShadowRate SelectedShadow SourceSelection

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-- Monotonicity of `CoupledBootstrapConclusion` in the reference class and the constants. -/
theorem bootstrapConclusion_mono {Z X O : Type*} [NormedAddCommGroup X] [PseudoMetricSpace O]
    {M : SlabModel Z X O} {Ref Ref' : Set Z} {d d' C C' : ℝ}
    (h : CoupledBootstrapConclusion M Ref d C) (hRef : Ref' ⊆ Ref) (hd : d' ≤ d) (hC : C ≤ C') :
    CoupledBootstrapConclusion M Ref' d' C' := by
  intro zs hzs zh hadm hmis
  have h0 : 0 ≤ M.mismatch zh zs :=
    add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (M.resB_nonneg _)) (M.resD_nonneg _))
      (M.harm_nonneg _)
  exact (h zs (hRef hzs) zh hadm (hmis.trans hd)).trans (mul_le_mul_of_nonneg_right hC h0)

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m V) (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')
variable (hS : SMSmooth SM) (hAsym : ∀ j a b v, Aco SM eX j a b v = Aco SM eX j b a v)
variable {k : ℕ} (hk : 4 ≤ k) {Tm : ℝ} (hTm : 0 < Tm) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
  (hKO : K ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁)

/-- The smallness constant `d_*` of `prop:coupled-bootstrap` (`coupled_bootstrap`). -/
def dBoot : ℝ :=
  Classical.choose (coupled_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁)

/-- The stability constant `C_*` of `prop:coupled-bootstrap` (`coupled_bootstrap`). -/
def CBoot : ℝ :=
  Classical.choose (Classical.choose_spec
    (coupled_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁))

theorem dBoot_pos : 0 < dBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ :=
  (Classical.choose_spec (Classical.choose_spec
    (coupled_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁))).1

theorem CBoot_nonneg : 0 ≤ CBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ :=
  (Classical.choose_spec (Classical.choose_spec
    (coupled_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁))).2.1

theorem boot_spec : CoupledBootstrapConclusion (slabModel SM eX eY eYD hS k Tm hTm)
    (refSet SM eX k Tm K R₁) (dBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁)
    (CBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁) :=
  (Classical.choose_spec (Classical.choose_spec
    (coupled_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁))).2.2

/-- **`prop:coupled-bootstrap` on a physical Cauchy tube**: if the tube's exact solutions lie in
the reference class and its declared constants are those of `prop:coupled-bootstrap`, the
bootstrap conclusion holds on the tube family. -/
theorem tube_bootstrap {Y : Type*} [Zero Y]
    {Ck : SeparationQuotient (NSpace (hkSeminorm (d := 3) (ι := Fin n) k 0)) → Y}
    (T : CauchyTube (slabModel SM eX eY eYD hS k Tm hTm) Ck)
    (hfam : T.family ⊆ refSet SM eX k Tm K R₁)
    (hd : T.dstar ≤ dBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁)
    (hC : CBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ ≤ T.Cstar) :
    CoupledBootstrapConclusion (slabModel SM eX eY eYD hS k Tm hTm) T.family T.dstar T.Cstar :=
  bootstrapConclusion_mono (boot_spec SM eX eY eYD hS hAsym hk hTm hK hKO hR₁) hfam hd hC

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

set_option hygiene false in
local notation "𝕄" => slabModel SM eX eY eYD hS k Tm hTm

set_option hygiene false in
local notation "𝕏" => SeparationQuotient (NSpace (hkSeminorm (d := 3) (ι := Fin n) k 0))

/-- **`thm:aposteriori-physical-shadow`** for the concrete slab model, with
`prop:coupled-bootstrap` discharged (`tube_bootstrap`). -/
theorem aposteriori_physical_shadow_closed {Ck : 𝕏 → Y} (T : CauchyTube 𝕄 Ck)
    (hfam : T.family ⊆ refSet SM eX k Tm K R₁)
    (hd : T.dstar ≤ dBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁)
    (hC : CBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ ≤ T.Cstar)
    {zh : Tuple m V S S'} (hadm : (𝕄).Admissible zh) (hharm : (𝕄).harm zh = 0) {mm : ℕ}
    {r B : ℝ} (R : ExactInitialConstraintReduction Ck ((𝕄).init zh) mm r B) {γ β η c τ : ℝ}
    (hγ : 0 < γ)
    (hA : ∀ v, γ * ‖v‖ ≤ ‖fderivWithin ℝ R.retained (closedBall 0 r) 0 v‖)
    (hmargin : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin mm)) r,
      ‖fderivWithin ℝ R.retained (closedBall 0 r) l -
        fderivWithin ℝ R.retained (closedBall 0 r) 0‖ ≤ γ / 2)
    (hres : ‖R.retained 0‖ ≤ β) (hrad : 2 * γ⁻¹ * β ≤ r) (hB : 0 ≤ B)
    (htube : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin mm)) (2 * γ⁻¹ * β), R.retained l = 0 →
      R.corr l ∈ T.Creg ∩ T.nbhd)
    (hc : 0 < c) (hτ : 0 < τ) (hforce : (𝕄).resB zh + (𝕄).resD zh ≤ η)
    (hsmall : shadowBudget B γ β c τ η ≤ T.stabilityRadius c τ) :
    ∃ l, (l ∈ closedBall (0 : EuclideanSpace ℝ (Fin mm)) (2 * γ⁻¹ * β) ∧ R.retained l = 0) ∧
      (∀ l', l' ∈ closedBall (0 : EuclideanSpace ℝ (Fin mm)) (2 * γ⁻¹ * β) ∧
        R.retained l' = 0 → l' = l) ∧
      Ck (R.corr l) = 0 ∧ ‖R.corr l - (𝕄).init zh‖ ≤ 2 * B * γ⁻¹ * β ∧
      (𝕄).IsExact (T.evolve (R.corr l)) ∧ (𝕄).init (T.evolve (R.corr l)) = R.corr l ∧
      (∀ z, (𝕄).IsExact z → (𝕄).init z = R.corr l → z = T.evolve (R.corr l)) ∧
      dist ((𝕄).obs zh) ((𝕄).obs (T.evolve (R.corr l))) ≤
        T.shadowConst c τ * shadowBudget B γ β c τ η :=
  aposteriori_physical_shadow _ T
    (tube_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ T hfam hd hC) hadm hharm R hγ hA
    hmargin hres hrad hB htube hc hτ hforce hsmall

/-- **`cor:shadow-harmonic-defect`** for the concrete slab model, with `prop:coupled-bootstrap`
discharged (`tube_bootstrap`). -/
theorem shadow_harmonic_defect_closed {Ck : 𝕏 → Y} (T : CauchyTube 𝕄 Ck)
    (hfam : T.family ⊆ refSet SM eX k Tm K R₁)
    (hd : T.dstar ≤ dBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁)
    (hC : CBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ ≤ T.Cstar)
    {zh : Tuple m V S S'} (hadm : (𝕄).Admissible zh) {x0 : 𝕏} {mm : ℕ} {r B : ℝ}
    (R : ExactInitialConstraintReduction Ck x0 mm r B)
    (A : EuclideanSpace ℝ (Fin mm) →L[ℝ] EuclideanSpace ℝ (Fin mm)) {γ β ζ η c τ : ℝ}
    (hγ : 0 < γ) (hA : ∀ v, γ * ‖v‖ ≤ ‖A v‖)
    (hmargin : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin mm)) r,
      ‖fderivWithin ℝ R.retained (closedBall 0 r) l - A‖ ≤ γ / 2)
    (hres : ‖R.retained 0‖ ≤ β) (hrad : 2 * γ⁻¹ * β ≤ r) (hB : 0 ≤ B)
    (hbase : ‖(𝕄).init zh - x0‖ ≤ ζ)
    (htube : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin mm)) (2 * γ⁻¹ * β), R.retained l = 0 →
      R.corr l ∈ T.Creg ∩ T.nbhd)
    (hc : 0 < c) (hτ : 0 < τ) (hforce : (𝕄).resB zh + (𝕄).resD zh ≤ η)
    (hsmall : harmonicBudget ζ B γ β c τ η ((𝕄).harm zh) ≤ T.stabilityRadius c τ) :
    ∃ l, (l ∈ closedBall (0 : EuclideanSpace ℝ (Fin mm)) (2 * γ⁻¹ * β) ∧ R.retained l = 0) ∧
      (∀ l', l' ∈ closedBall (0 : EuclideanSpace ℝ (Fin mm)) (2 * γ⁻¹ * β) ∧
        R.retained l' = 0 → l' = l) ∧
      Ck (R.corr l) = 0 ∧ ‖R.corr l - x0‖ ≤ 2 * B * γ⁻¹ * β ∧
      (𝕄).IsExact (T.evolve (R.corr l)) ∧ (𝕄).init (T.evolve (R.corr l)) = R.corr l ∧
      (∀ z, (𝕄).IsExact z → (𝕄).init z = R.corr l → z = T.evolve (R.corr l)) ∧
      dist ((𝕄).obs zh) ((𝕄).obs (T.evolve (R.corr l))) ≤
        T.shadowConst c τ * harmonicBudget ζ B γ β c τ η ((𝕄).harm zh) :=
  shadow_harmonic_defect _ T
    (tube_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ T hfam hd hC) hadm R A hγ hA
    hmargin hres hrad hB hbase htube hc hτ hforce hsmall

/-- **`cor:aposteriori-shadow-rate`** for the concrete slab model, with `prop:coupled-bootstrap`
discharged (`tube_bootstrap`). -/
theorem aposteriori_shadow_rate_closed {Ck : 𝕏 → Y} (T : CauchyTube 𝕄 Ck)
    (hfam : T.family ⊆ refSet SM eX k Tm K R₁)
    (hd : T.dstar ≤ dBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁)
    (hC : CBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ ≤ T.Cstar)
    {ι : Type*} {l : Filter ι} {h s ε β : ι → ℝ} (hh : Tendsto h l (𝓝[>] 0))
    (zh : ι → Tuple m V S S') (hadm : ∀ i, (𝕄).Admissible (zh i))
    (hharm : ∀ i, (𝕄).harm (zh i) = 0)
    {mm : ι → ℕ} {r B γ CR Cs Cβ c τ : ℝ}
    (R : ∀ i, ExactInitialConstraintReduction Ck ((𝕄).init (zh i)) (mm i) r B) (hγ : 0 < γ)
    (hA : ∀ i, ∀ v, γ * ‖v‖ ≤ ‖fderivWithin ℝ (R i).retained (closedBall 0 r) 0 v‖)
    (hmargin : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (mm i))) r,
      ‖fderivWithin ℝ (R i).retained (closedBall 0 r) x -
        fderivWithin ℝ (R i).retained (closedBall 0 r) 0‖ ≤ γ / 2)
    (hres : ∀ i, ‖(R i).retained 0‖ ≤ β i) (hrad : ∀ i, 2 * γ⁻¹ * β i ≤ r) (hB : 0 ≤ B)
    (htube : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (mm i))) (2 * γ⁻¹ * β i),
      (R i).retained x = 0 → (R i).corr x ∈ T.Creg ∩ T.nbhd)
    (hc : 0 < c) (hτ : 0 < τ) (hCR : 0 ≤ CR) (hCs : 0 ≤ Cs)
    (hrate : ∀ᶠ i in l, 0 ≤ s i ∧ s i ≤ Cs * h i ∧ 0 ≤ ε i ∧ ε i ≤ CR * (s i + h i) ∧
      β i ≤ Cβ * h i ^ (1 / 2 : ℝ))
    (hforce : ∀ i, (𝕄).resB (zh i) + (𝕄).resD (zh i) ≤ shadowEta CR 4 10 (ε i)) :
    ∃ C : ℝ, ∀ᶠ i in l, ∃ x : EuclideanSpace ℝ (Fin (mm i)), (R i).retained x = 0 ∧
      Ck ((R i).corr x) = 0 ∧ (𝕄).IsExact (T.evolve ((R i).corr x)) ∧
      (∀ z, (𝕄).IsExact z → (𝕄).init z = (R i).corr x → z = T.evolve ((R i).corr x)) ∧
      dist ((𝕄).obs (zh i)) ((𝕄).obs (T.evolve ((R i).corr x))) ≤ C * h i ^ (1 / 2 : ℝ) :=
  aposteriori_shadow_rate _ T
    (tube_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ T hfam hd hC) hh zh hadm hharm R
    hγ hA hmargin hres hrad hB htube hc hτ hCR hCs hrate hforce

variable {Ω 𝒳 : Type*} [Fintype Ω] [Fintype 𝒳] [DecidableEq 𝒳] [DecidableEq Ω]

/-- **`thm:native-selected-shadow`** for the concrete slab model, with `prop:coupled-bootstrap`
discharged (`tube_bootstrap`). -/
theorem native_selected_shadow_closed (proc : FiniteAcceptedProcess Ω 𝒳)
    (a g Vf : 𝒳 → ℝ) (rr : ℕ → 𝒳 → ℝ) {Am Ap κ δ sh Rr β : ℝ}
    (ha : ∀ x, Am ≤ a x ∧ a x ≤ Ap) (hκ : 0 < κ) (hδ : 0 < δ) (hsh : 0 < sh) (hRr : 0 < Rr)
    (hβ : 0 < β) (hg : ∀ x, 0 ≤ g x) (hV : ∀ x, 0 ≤ Vf x) (J : ℕ) (hJ : 0 < J)
    (hdrift : ∀ j < J, ∀ x, 0 < proc.survivingMass j x →
      proc.actionDrift a j x ≤ -(κ * δ) * g x ^ 2 + δ * rr j x)
    {Ck : 𝕏 → Y} (T : CauchyTube 𝕄 Ck)
    (hfam : T.family ⊆ refSet SM eX k Tm K R₁)
    (hd : T.dstar ≤ dBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁)
    (hC : CBoot SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ ≤ T.Cstar)
    (zrec : 𝒳 → Tuple m V S S') (hadm : ∀ x, (𝕄).Admissible (zrec x))
    (hharm : ∀ x, (𝕄).harm (zrec x) = 0)
    {mm : 𝒳 → ℕ} {r B γ : ℝ}
    (R : ∀ x, ExactInitialConstraintReduction Ck ((𝕄).init (zrec x)) (mm x) r B) (hγ : 0 < γ)
    (hA : ∀ x, ∀ v, γ * ‖v‖ ≤ ‖fderivWithin ℝ (R x).retained (closedBall 0 r) 0 v‖)
    (hmargin : ∀ x, ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin (mm x))) r,
      ‖fderivWithin ℝ (R x).retained (closedBall 0 r) l -
        fderivWithin ℝ (R x).retained (closedBall 0 r) 0‖ ≤ γ / 2)
    (hrad : 2 * γ⁻¹ * β ≤ r) (hB : 0 ≤ B)
    (htube : ∀ x, ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin (mm x))) (2 * γ⁻¹ * β),
      (R x).retained l = 0 → (R x).corr l ∈ T.Creg ∩ T.nbhd)
    (sel : Ω → ℕ)
    (hsel : ∀ ϖ ∈ proc.S J, sel ϖ < J ∧ ∀ j < J,
      FiniteAcceptedProcess.score g Vf (fun x => ‖(R x).retained 0‖ ^ 2) sh Rr β
          (proc.X (sel ϖ) ϖ) ≤
        FiniteAcceptedProcess.score g Vf (fun x => ‖(R x).retained 0‖ ^ 2) sh Rr β (proc.X j ϖ))
    {h CR ks s c τ : ℝ} (εr : 𝒳 → ℝ) (hk0 : 0 ≤ ks) (hks : ks + 1 ≤ s) (hCR : 0 ≤ CR)
    (hupgrade : ∀ x, Vf x ≤ Rr ^ 2 → g x ≤ sh →
      0 ≤ εr x ∧ εr x ≤ CR * (sh + h) ∧
        (𝕄).resB (zrec x) + (𝕄).resD (zrec x) ≤ shadowEta CR ks s (εr x))
    (hc : 0 < c) (hτ : 0 < τ)
    (hsmall : selectedBudget B γ β c τ CR ks s sh h ≤ T.stabilityRadius c τ) :
    (∑ ϖ ∈ Finset.univ.filter (fun ϖ => ϖ ∉ proc.S J ∨
        ¬ (g (proc.X (sel ϖ) ϖ) ≤ sh ∧ Vf (proc.X (sel ϖ) ϖ) ≤ Rr ^ 2 ∧
          ‖(R (proc.X (sel ϖ) ϖ)).retained 0‖ ^ 2 ≤ β ^ 2)), proc.P ϖ
      ≤ proc.exitProbability J + (Ap - Am) / (κ * δ * J * sh ^ 2)
        + proc.occupation J rr / (κ * sh ^ 2)
        + proc.occupation J (fun _ x => Vf x) / Rr ^ 2
        + proc.occupation J (fun _ x => ‖(R x).retained 0‖ ^ 2) / β ^ 2) ∧
    ∀ ϖ ∈ proc.S J, g (proc.X (sel ϖ) ϖ) ≤ sh → Vf (proc.X (sel ϖ) ϖ) ≤ Rr ^ 2 →
      ‖(R (proc.X (sel ϖ) ϖ)).retained 0‖ ≤ β →
      ∃ l : EuclideanSpace ℝ (Fin (mm (proc.X (sel ϖ) ϖ))),
        (l ∈ closedBall 0 (2 * γ⁻¹ * β) ∧ (R (proc.X (sel ϖ) ϖ)).retained l = 0) ∧
        Ck ((R (proc.X (sel ϖ) ϖ)).corr l) = 0 ∧
        ‖(R (proc.X (sel ϖ) ϖ)).corr l - (𝕄).init (zrec (proc.X (sel ϖ) ϖ))‖ ≤
          2 * B * γ⁻¹ * β ∧
        (𝕄).IsExact (T.evolve ((R (proc.X (sel ϖ) ϖ)).corr l)) ∧
        (∀ z, (𝕄).IsExact z → (𝕄).init z = (R (proc.X (sel ϖ) ϖ)).corr l →
          z = T.evolve ((R (proc.X (sel ϖ) ϖ)).corr l)) ∧
        dist ((𝕄).obs (zrec (proc.X (sel ϖ) ϖ)))
            ((𝕄).obs (T.evolve ((R (proc.X (sel ϖ) ϖ)).corr l))) ≤
          T.shadowConst c τ * selectedBudget B γ β c τ CR ks s sh h :=
  native_selected_shadow proc a g Vf rr ha hκ hδ hsh hRr hβ hg hV J hJ hdrift _ T
    (tube_bootstrap SM eX eY eYD hS hAsym hk hTm hK hKO hR₁ T hfam hd hC) zrec hadm hharm R hγ
    hA hmargin hrad hB htube sel hsel εr hk0 hks hCR hupgrade hc hτ hsmall

end RenewalGeometry.CoupledBootstrap.ShadowClosed
