/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianOperatorGraphCanonicalHeatSemigroup
import NCG.Grand.FiniteHermitianSemigroupEndpoint
import NCG.Grand.OperatorGraphResolventHeatSemigroup
import NCG.Grand.VaryingHilbertSemigroupZeroEndpoint
import NCG.Grand.VaryingHilbertStrongBoundedness
import NCG.Grand.ResolventShiftPropagation

/-!
# Canonical graph-resolvent heat convergence through time zero

The positive-time heat functional calculus attached to a graph resolvent does not itself have
the identity as its value at zero: its scalar multiplier was deliberately defined only for
positive time.  This file adjoins the correct zero value and proves uniform strong convergence
on arbitrary compact sets of nonnegative times.

The endpoint argument uses the dense range of one positive-shift resolvent.  Stage source
vectors are obtained by applying the corresponding finite resolvents to strongly convergent
approximations of their limit preimages.  Their generator images are uniformly bounded by the
resolvent equation, giving a common linear modulus at zero.
-/

open Filter Set Topology Matrix
open scoped ComplexOrder ENNReal Norms.L2Operator

noncomputable section

namespace NCG.VaryingHilbert

/-- The canonical graph-resolvent heat family with its strongly continuous value at time zero. -/
def operatorGraphResolventHeatNonnegative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (R : E →L[ℂ] E) (b t : ℝ) : E →L[ℂ] E :=
  if t = 0 then ContinuousLinearMap.id ℂ E
  else operatorGraphResolventHeat R b t

@[simp] theorem operatorGraphResolventHeatNonnegative_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (R : E →L[ℂ] E) (b : ℝ) :
    operatorGraphResolventHeatNonnegative R b 0 = ContinuousLinearMap.id ℂ E := by
  simp [operatorGraphResolventHeatNonnegative]

theorem operatorGraphResolventHeatNonnegative_of_ne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (R : E →L[ℂ] E) (b t : ℝ) (ht : t ≠ 0) :
    operatorGraphResolventHeatNonnegative R b t =
      operatorGraphResolventHeat R b t := by
  simp [operatorGraphResolventHeatNonnegative, ht]

/-- The zero-extended canonical heat family remains contractive at every nonnegative time. -/
theorem norm_operatorGraphResolventHeatNonnegative_le_one
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t)
    (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A b f (R f)) :
    ‖operatorGraphResolventHeatNonnegative R b t‖ ≤ 1 := by
  by_cases ht0 : t = 0
  · subst t
    simpa [operatorGraphResolventHeatNonnegative] using
      (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ E‖ ≤ 1)
  · rw [operatorGraphResolventHeatNonnegative_of_ne R b t ht0]
    exact norm_operatorGraphResolventHeat_le_one D A b t hb ht R hequation

namespace System

universe u v x z

variable {iota : ℕ → Type u}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type x} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
variable {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- Finite Hermitian graph-Mosco convergence implies uniform strong convergence on compact
sets of nonnegative times to the correctly zero-extended canonical heat semigroup. -/
theorem
StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_canonicalResolventHeat_nonnegative
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))
    (G : ∀ n, Matrix (iota n) (iota n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (iota n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (hD : Dense (D : Set H))
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (iota n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b : ℝ) (hb : 0 < b)
    (s : Set ℝ) (hs : IsCompact s) (hsNonneg : ∀ t ∈ s, 0 ≤ t) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n)))
      (fun t ↦ operatorGraphResolventHeatNonnegative (R b) b t) s := by
  classical
  let Sn : ∀ n, ℝ →
      EuclideanSpace ℂ (iota n) →L[ℂ] EuclideanSpace ℂ (iota n) :=
    fun n t ↦ NormedSpace.exp ((-(t : ℂ)) •
      Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n))
  let S : ℝ → H →L[ℂ] H :=
    fun t ↦ operatorGraphResolventHeatNonnegative (R b) b t
  have hresolvents : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) (R lam) :=
    J.operatorGraphMosco_strongResolvents_allPositive
      Dn An D A
      (fun lam n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) R hmosco hstageEquation hlimitEquation
  have hdenseStage : J.IsAsymptoticallyDense :=
    (hmosco id tendsto_id).asymptoticallyDense
  let input : H → ∀ n, EuclideanSpace ℂ (iota n) :=
    fun f ↦ Classical.choose (hdenseStage f)
  have hinput : ∀ f : H, J.StronglyConverges (input f) f :=
    fun f ↦ Classical.choose_spec (hdenseStage f)
  let Core : Set H := Set.range (R b)
  have hCoreDense : Dense Core :=
    operatorGraphResolvent_denseRange D A b (R b) hD
      (hlimitEquation b hb)
  let preimage : H → H := fun d ↦
    if hd : d ∈ Core then Classical.choose hd else 0
  have hpreimage : ∀ d ∈ Core, R b (preimage d) = d := by
    intro d hd
    simp only [preimage, dif_pos hd]
    exact Classical.choose_spec hd
  let source : H → ∀ n, EuclideanSpace ℂ (iota n) :=
    fun d n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
      (G n) b (input (preimage d) n)
  have hsource : ∀ d ∈ Core, J.StronglyConverges (source d) d := by
    intro d hd
    have h := hresolvents b hb (input (preimage d)) (preimage d)
      (hinput (preimage d))
    simpa only [source, hpreimage d hd] using h
  apply
    StrongOperatorConvergesUniformlyOn.of_positive_truncations_and_dense_zero_core
      J Sn S s hsNonneg
  · intro n t ht
    exact NCG.ImplicitEuler.norm_finiteHermitian_exp_neg_le_one
      (G n) (hG n) t (hsNonneg t ht)
  · intro t ht
    exact norm_operatorGraphResolventHeatNonnegative_le_one
      D A b t hb (hsNonneg t ht) (R b) (hlimitEquation b hb)
  · exact hCoreDense
  · exact hsource
  · intro d hd
    let gen : ∀ n, EuclideanSpace ℂ (iota n) :=
      fun n ↦ input (preimage d) n - (b : ℂ) • source d n
    have hgen : J.StronglyConverges gen (preimage d - (b : ℂ) • d) := by
      exact StronglyConverges.sub J (hinput (preimage d))
        (StronglyConverges.smul J (b : ℂ) (hsource d hd))
    obtain ⟨C, hCpos, hCbound⟩ := hgen.exists_pos_uniform_norm_bound J
    refine ⟨C, hCpos.le, Filter.Eventually.of_forall fun n t ht ↦ ?_⟩
    rw [dist_eq_norm]
    calc
      ‖Sn n t (source d n) - source d n‖
          ≤ t * ‖Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n)
              (source d n)‖ :=
        NCG.ImplicitEuler.norm_finiteHermitian_exp_neg_apply_sub_self_le
          (G n) (hG n) t (hsNonneg t ht) (source d n)
      _ = t * ‖gen n‖ := by
        congr 2
        rw [NCG.ImplicitEuler.generator_apply_finiteHermitianShiftedResolventOperator
          (G n) (hG n) b hb (input (preimage d) n)]
      _ ≤ t * C :=
        mul_le_mul_of_nonneg_left (hCbound n) (hsNonneg t ht)
  · intro d hd
    let gen : ∀ n, EuclideanSpace ℂ (iota n) :=
      fun n ↦ input (preimage d) n - (b : ℂ) • source d n
    have hgen : J.StronglyConverges gen (preimage d - (b : ℂ) • d) := by
      exact StronglyConverges.sub J (hinput (preimage d))
        (StronglyConverges.smul J (b : ℂ) (hsource d hd))
    obtain ⟨C, hCpos, hCbound⟩ := hgen.exists_pos_uniform_norm_bound J
    refine ⟨C, hCpos.le, fun t ht ↦ ?_⟩
    by_cases ht0 : t = 0
    · subst t
      simp [S, operatorGraphResolventHeatNonnegative]
    · have htPos : 0 < t := lt_of_le_of_ne (hsNonneg t ht) (Ne.symm ht0)
      have hpositive :=
        StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_canonicalResolventHeat
          J G hG Dn An D A hD R hmosco hstageEquation hlimitEquation b hb
          ({t} : Set ℝ) isCompact_singleton (by
            intro u hu
            simp only [Set.mem_singleton_iff] at hu
            subst u
            exact htPos)
      have hpoint := (hpositive (source d) d (hsource d hd)).tendsto_at
        (show t ∈ ({t} : Set ℝ) by simp)
      have hsourcePoint : Tendsto
          (fun n ↦ J.embedding n (source d n)) atTop (𝓝 d) :=
        hsource d hd
      have hdist : Tendsto
          (fun n ↦ dist
            (J.embedding n (Sn n t (source d n)))
            (J.embedding n (source d n)))
          atTop
          (𝓝 (dist (operatorGraphResolventHeat (R b) b t d) d)) := by
        exact hpoint.dist hsourcePoint
      have hbound : ∀ᶠ n in atTop,
          dist
            (J.embedding n (Sn n t (source d n)))
            (J.embedding n (source d n)) ≤ t * C := by
        filter_upwards [] with n
        rw [LinearIsometry.dist_map, dist_eq_norm]
        calc
          ‖Sn n t (source d n) - source d n‖
              ≤ t * ‖Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n)
                  (source d n)‖ :=
            NCG.ImplicitEuler.norm_finiteHermitian_exp_neg_apply_sub_self_le
              (G n) (hG n) t htPos.le (source d n)
          _ = t * ‖gen n‖ := by
            congr 2
            rw [NCG.ImplicitEuler.generator_apply_finiteHermitianShiftedResolventOperator
              (G n) (hG n) b hb (input (preimage d) n)]
          _ ≤ t * C :=
            mul_le_mul_of_nonneg_left (hCbound n) htPos.le
      have hlimit :
          dist (operatorGraphResolventHeat (R b) b t d) d ≤ t * C :=
        le_of_tendsto hdist hbound
      simpa [S, operatorGraphResolventHeatNonnegative, ht0] using hlimit
  · intro delta hdelta
    have hsdelta : IsCompact (s ∩ Ici delta) :=
      hs.inter_right isClosed_Ici
    have hsdeltaPos : ∀ t ∈ s ∩ Ici delta, 0 < t := by
      intro t ht
      exact hdelta.trans_le ht.2
    have hpositive :=
      StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_canonicalResolventHeat
        J G hG Dn An D A hD R hmosco hstageEquation hlimitEquation b hb
        (s ∩ Ici delta) hsdelta hsdeltaPos
    intro x xlim hx
    exact (hpositive x xlim hx).congr_right fun t ht ↦ by
      rw [show S t =
        operatorGraphResolventHeatNonnegative (R b) b t by rfl]
      rw [operatorGraphResolventHeatNonnegative_of_ne
        (R b) b t (ne_of_gt (hsdeltaPos t ht))]

end System
end NCG.VaryingHilbert
