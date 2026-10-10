/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallUhlenbeckRescale

/-!
# Uhlenbeck's small-energy gauge theorem for structure groups: packaging
  (stage D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure for `prop:critical-uhlenbeck` and `thm:critical-quotient-defect` of the
Einstein–Standard-Model action-closure manuscript.

* `IsGaugeStructure G 𝔤` — the structure data used by the proof: `𝔤` a real Lie subalgebra of
  skew-Hermitian matrices, `G` closed, `G·G ⊆ G`, `exp 𝔤 ⊆ G`, `Ad_G 𝔤 ⊆ 𝔤` (satisfied by every
  closed — hence compact — subgroup `G ⊆ U(m)` together with a Lie subalgebra of its Lie algebra
  that is `Ad_G`-invariant, e.g. its full Lie algebra);
* `exists_lieBasis` — a Lie basis `L` with `L.lieAlg = 𝔤` (basis, linear coordinates on all of
  `M_m(ℂ)`, structure constants), and `gaugeGroupData_of` — the corresponding `GaugeGroupData`;
* `UhlenbeckHigherBounds m G` — the uniform `H⁶` bounds of the closedness step on the unit ball
  for every Lie basis with gauge group data;
* `uhlenbeckIn_of_higherBounds` (**main result**):
  `IsGaugeStructure G 𝔤 → UhlenbeckHigherBounds m G → UhlenbeckSmallEnergyGaugeIn m G 𝔤`;
* `unitary_isGaugeStructure` and `uhlenbeck_of_higherBounds` — the unitary case:
  `UhlenbeckHigherBounds m U(m) → UhlenbeckSmallEnergyGauge m`.
-/

open MeasureTheory Filter Topology Set Matrix NormedSpace
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.UhlenbeckPackage

open SobolevOpen CriticalGauge UhlenbeckGauge BallAlg UhlenbeckBall UhlenbeckRescale

set_option linter.unusedSectionVars false

variable {m : ℕ}

instance instFactZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- **Structure data of a gauge theory**: a real Lie subalgebra `𝔤` of skew-Hermitian matrices
and a closed set `G` of matrices, closed under products, containing `exp 𝔤`, with `Ad_G 𝔤 ⊆ 𝔤`. -/
structure IsGaugeStructure (G : Set (Matrix (Fin m) (Fin m) ℂ))
    (𝔤 : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ)) : Prop where
  skew : ∀ X ∈ 𝔤, star X = -X
  bracket : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤
  closed : IsClosed G
  mul_mem : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G
  exp_mem : ∀ X ∈ 𝔤, exp X ∈ G
  ad_mem : ∀ g ∈ G, ∀ X ∈ 𝔤, g * X * star g ∈ 𝔤

/-- **Existence of Lie bases.** -/
theorem exists_lieBasis (𝔤 : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ))
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) :
    ∃ (d : ℕ) (L : LieBasis m d), L.lieAlg = 𝔤 := by
  classical
  set d := Module.finrank ℝ 𝔤
  set b : Module.Basis (Fin d) ℝ 𝔤 := Module.finBasis ℝ 𝔤
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl 𝔤
  set P : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] 𝔤 := Submodule.linearProjOfIsCompl 𝔤 q hq
  have hbm : ∀ a c, (b a : Matrix (Fin m) (Fin m) ℂ) * b c - b c * b a ∈ 𝔤 := fun a c =>
    hbr _ (b a).2 _ (b c).2
  refine ⟨d, {
    e := fun a => (b a : Matrix (Fin m) (Fin m) ℂ)
    κ := b.equivFun.toLinearMap ∘ₗ P
    κ_e := fun a => ?_
    f := fun a c k => b.repr ⟨_, hbm a c⟩ k
    bracket := fun a c => ?_ }, ?_⟩
  · simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [show P (b a : Matrix (Fin m) (Fin m) ℂ) = b a from
      Submodule.linearProjOfIsCompl_apply_left hq (b a)]
    funext k
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  · have h := b.sum_repr ⟨_, hbm a c⟩
    have h' := congrArg (fun x : 𝔤 => (x : Matrix (Fin m) (Fin m) ℂ)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    exact h'.symm
  · show Submodule.span ℝ (Set.range fun a => (b a : Matrix (Fin m) (Fin m) ℂ)) = 𝔤
    rw [show (Set.range fun a => (b a : Matrix (Fin m) (Fin m) ℂ)) = 𝔤.subtype '' Set.range b by
      rw [← Set.range_comp]; rfl, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

theorem gaugeGroupData_of {d : ℕ} (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    {𝔤 : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ)} (hL : L.lieAlg = 𝔤) (hS : IsGaugeStructure G 𝔤) :
    GaugeGroupData L G := by
  have he : ∀ b, L.e b ∈ 𝔤 := fun b => hL ▸ Submodule.subset_span ⟨b, rfl⟩
  exact ⟨fun b => hS.skew _ (he b), hS.closed, hS.mul_mem, fun X hX => hS.exp_mem X (hL ▸ hX),
    fun g hg X hX => hL ▸ hS.ad_mem g hg X (hL ▸ hX)⟩

/-- **The uniform higher bounds on the unit ball, for every Lie basis with gauge data** (the
closedness input of the continuity method, `CoulombHigherBounds`). -/
def UhlenbeckHigherBounds (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  ∀ (d : ℕ) (L : LieBasis m d), GaugeGroupData L G → CoulombHigherBounds 0 1 L G

/-- **Uhlenbeck's small-energy Coulomb gauge theorem for a structure group, from the uniform
higher bounds.** -/
theorem uhlenbeckIn_of_higherBounds {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    {𝔤 : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ)} (hS : IsGaugeStructure G 𝔤)
    (hHB : UhlenbeckHigherBounds m G) :
    UhlenbeckSmallEnergyGaugeIn m G 𝔤 := by
  obtain ⟨d, L, hL⟩ := exists_lieBasis 𝔤 hS.bracket
  have hGD := gaugeGroupData_of L hL hS
  have h := uhlenbeckBallIn_of_bounds (c := 0) (r := 1) L hGD (hHB d L hGD)
  rw [hL] at h
  refine uhlenbeckIn_of_ball01 (fun s X hX => ?_) h
  rw [show ((s : ℂ) • X) = s • X from (Complex.coe_smul s X)]
  exact 𝔤.smul_mem s hX

/-! ### The unitary group -/

/-- The real Lie algebra `𝔲(m)` of skew-Hermitian matrices. -/
def skewSub (m : ℕ) : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) where
  carrier := {X | star X = -X}
  add_mem' := fun {X Y} hX hY => by
    simp only [mem_setOf_eq] at *
    rw [star_add, hX, hY, neg_add]
  zero_mem' := by simp
  smul_mem' := fun s X hX => by
    simp only [mem_setOf_eq] at *
    rw [star_smul, hX, star_trivial, smul_neg]

theorem isClosed_unitaryGroup : IsClosed (unitaryGroup (Fin m) ℂ : Set (Matrix (Fin m) (Fin m) ℂ)) := by
  have hc : Continuous fun U : Matrix (Fin m) (Fin m) ℂ => star U :=
    continuous_id.matrix_conjTranspose
  have e : (unitaryGroup (Fin m) ℂ : Set (Matrix (Fin m) (Fin m) ℂ)) =
      {U | star U * U = 1} ∩ {U | U * star U = 1} := by
    ext U
    simp only [SetLike.mem_coe, mem_inter_iff, mem_setOf_eq]
    exact Unitary.mem_iff
  rw [e]
  exact (isClosed_eq (hc.matrix_mul continuous_id) continuous_const).inter
    (isClosed_eq (continuous_id.matrix_mul hc) continuous_const)

theorem exp_mem_unitaryGroup {X : Matrix (Fin m) (Fin m) ℂ} (hX : star X = -X) :
    exp X ∈ unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h1 : star (exp X) = exp (-X) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← Matrix.star_eq_conjTranspose,
      hX]
  rw [h1, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

theorem unitary_isGaugeStructure (m : ℕ) :
    IsGaugeStructure (unitaryGroup (Fin m) ℂ) (skewSub m) where
  skew := fun X hX => hX
  bracket := fun X hX Y hY => by
    show star (X * Y - Y * X) = -(X * Y - Y * X)
    have hX' : star X = -X := hX
    have hY' : star Y = -Y := hY
    rw [star_sub, star_mul, star_mul, hX', hY']
    noncomm_ring
  closed := isClosed_unitaryGroup
  mul_mem := fun g hg h hh => Submonoid.mul_mem _ hg hh
  exp_mem := fun X hX => exp_mem_unitaryGroup hX
  ad_mem := fun g hg X hX => by
    show star (g * X * star g) = -(g * X * star g)
    have hX' : star X = -X := hX
    rw [star_mul, star_mul, star_star, hX']
    noncomm_ring

/-- **Uhlenbeck's theorem for `U(m)` from the uniform higher bounds.** -/
theorem uhlenbeck_of_higherBounds (hHB : UhlenbeckHigherBounds m (unitaryGroup (Fin m) ℂ)) :
    UhlenbeckSmallEnergyGauge m := by
  obtain ⟨εU, hεU, CU, hU⟩ := uhlenbeckIn_of_higherBounds (unitary_isGaugeStructure m) hHB
  exact ⟨εU, hεU, CU, fun c r hr => by
    obtain ⟨Cr, hCr⟩ := hU c r hr
    exact ⟨Cr, fun A hA hE => hCr A hA (fun μ y => hA.skew μ y) hE⟩⟩

end RenewalGeometry.BallAnalysis.UhlenbeckPackage
