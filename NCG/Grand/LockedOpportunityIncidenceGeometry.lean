/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.LockedIncidenceProfile
import NCG.Grand.LockedOddPauli
import NCG.Grand.NativeGenerations
import NCG.Matter.EdgeResponse

/-!
# Locked opportunity incidence geometry

This module closes the packet-level parts of the locked incidence profile:
cross-edge commutation is an independent datum not seen by marginal Pauli
Grams, the `K₄` cut/cycle split exports only the cut component to endpoints,
and a scalar standard-triplet Gram has joint rank three times its multiplicity
Gram rank.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

namespace NCG
namespace LockedOpportunityIncidenceGeometry

/-- Concrete Schur lemma for the three-dimensional standard triplet: commuting
with the diagonal and symmetric transposition generators forces a scalar. -/
theorem standardTriplet_schur_scalar (X : Matrix (Fin 3) (Fin 3) ℂ)
    (h11 : X * !![1, 0, 0; 0, 0, 0; 0, 0, 0]
      = !![1, 0, 0; 0, 0, 0; 0, 0, 0] * X)
    (h22 : X * !![0, 0, 0; 0, 1, 0; 0, 0, 0]
      = !![0, 0, 0; 0, 1, 0; 0, 0, 0] * X)
    (h12 : X * !![0, 1, 0; 1, 0, 0; 0, 0, 0]
      = !![0, 1, 0; 1, 0, 0; 0, 0, 0] * X)
    (h23 : X * !![0, 0, 0; 0, 0, 1; 0, 1, 0]
      = !![0, 0, 0; 0, 0, 1; 0, 1, 0] * X) :
    X = X 0 0 • 1 :=
  commute_sym_scalar X h11 h22 h12 h23

/-- Cross-edge commutator Hilbert--Schmidt residual, indexed without double
counting by ordered edge pairs. -/
noncomputable def crossEdgeCommutatorResidual {E A H : Type*}
    [Fintype E] [LinearOrder E] [Fintype A] [Fintype H] [DecidableEq H]
    (sigma : E → A → Matrix H H ℂ) : ℝ :=
  ∑ p : {p : E × E // p.1 < p.2}, ∑ a, ∑ b,
    ‖sigma p.1.1 a * sigma p.1.2 b -
      sigma p.1.2 b * sigma p.1.1 a‖ ^ 2

/-- The parallelization residual vanishes exactly when all distinct-edge axes
commute. -/
theorem crossEdgeCommutatorResidual_eq_zero_iff {E A H : Type*}
    [Fintype E] [LinearOrder E] [Fintype A] [Fintype H] [DecidableEq H]
    (sigma : E → A → Matrix H H ℂ) :
    crossEdgeCommutatorResidual sigma = 0 ↔
      ∀ e f, e < f → ∀ a b,
        sigma e a * sigma f b = sigma f b * sigma e a := by
  classical
  constructor
  · intro h e f hef a b
    have hpall := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))).mp
      (show (∑ p : {p : E × E // p.1 < p.2}, ∑ a, ∑ b,
        ‖sigma p.1.1 a * sigma p.1.2 b -
          sigma p.1.2 b * sigma p.1.1 a‖ ^ 2) = 0 from h)
    have hp := hpall ⟨(e, f), hef⟩ (Finset.mem_univ _)
    have haall := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mp hp
    have ha := haall a (Finset.mem_univ _)
    have hball := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp ha
    have hb := hball b (Finset.mem_univ _)
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hb
    exact hb
  · intro h
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))).mpr
    intro p _
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mpr
    intro a _
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mpr
    intro b _
    rw [h p.1.1 p.1.2 p.2 a b, sub_self, norm_zero]
    norm_num

/-- The two Pauli matrices used for the explicit marginal-versus-joint
counterexample. -/
def pauliX2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def pauliZ2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Identical nonzero marginal one-axis Grams permit both a commuting and a
noncommuting two-edge realization.  Thus local packet Grams do not decide
simultaneous edge clocks. -/
theorem marginalGrams_do_not_determine_crossEdgeCommutation :
    pauliZ2ᴴ * pauliZ2 = 1 ∧ pauliX2ᴴ * pauliX2 = 1 ∧
      pauliZ2 * pauliZ2 = pauliZ2 * pauliZ2 ∧
      pauliZ2 * pauliX2 ≠ pauliX2 * pauliZ2 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pauliZ2, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pauliX2, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two]
  constructor
  · rfl
  · intro h
    have hij := congrArg (fun M => M 0 1) h
    norm_num [pauliX2, pauliZ2, Matrix.mul_apply, Fin.sum_univ_two] at hij

/-- The range of a coordinatewise linear map is the finite product of the
individual ranges. -/
noncomputable def coordinatewiseRangeEquiv {K M N I : Type*}
    [Field K] [Fintype I] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    ↥(LinearMap.range (f.compLeft I)) ≃ₗ[K] (I → LinearMap.range f) where
  toFun y i := ⟨y.1 i, by
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x i, congrFun hx i⟩⟩
  invFun y := ⟨fun i => (y i).1, by
    refine ⟨fun i => (y i).2.choose, ?_⟩
    funext i
    exact (y i).2.choose_spec⟩
  left_inv y := by
    apply Subtype.ext
    rfl
  right_inv y := by
    funext i
    apply Subtype.ext
    rfl
  map_add' x y := by
    funext i
    apply Subtype.ext
    rfl
  map_smul' c x := by
    funext i
    apply Subtype.ext
    rfl

/-- A scalar `S₄` standard triplet multiplies the multiplicity rank by exactly
three.  This is the boxed `rank S_joint = 3 rank g` formula at the Gram-map
level. -/
theorem standardTriplet_jointRank {m : Type*} [Fintype m]
    (g : Matrix m m ℂ) :
    Module.finrank ℂ (LinearMap.range (g.mulVecLin.compLeft (Fin 3))) =
      3 * g.rank := by
  classical
  rw [LinearEquiv.finrank_eq (coordinatewiseRangeEquiv g.mulVecLin)]
  rw [Module.finrank_pi_fintype]
  simp only [Fin.sum_univ_three]
  change Module.finrank ℂ (LinearMap.range g.mulVecLin) +
      Module.finrank ℂ (LinearMap.range g.mulVecLin) +
      Module.finrank ℂ (LinearMap.range g.mulVecLin) =
    3 * Module.finrank ℂ (LinearMap.range g.mulVecLin)
  omega

/-- A cycle component annihilated by the endpoint boundary contributes no
tangential endpoint source; only the cut component survives. -/
theorem endpointSource_forgets_cycle {E V K : Type*}
    [Fintype E]
    (Qcut Qcycle : Matrix E K ℂ) (boundary : Matrix V E ℂ)
    (hcycle : boundary * Qcycle = 0) :
    boundary * (Qcut + Qcycle) = boundary * Qcut := by
  rw [Matrix.mul_add, hcycle, add_zero]

end LockedOpportunityIncidenceGeometry
end NCG
