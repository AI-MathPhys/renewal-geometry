/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.OperatorGraphMoscoResolventConvergence
import NCG.Grand.ENNRealOperatorGraphMoscoConverseFromOneShiftWeakEquation
import NCG.Grand.FiniteHermitianOperatorGraphCanonicalHeatSemigroup
import NCG.Grand.ENNRealClosedOperatorGraphEnergyLowerSemicontinuity
import NCG.Grand.ENNRealResolventOperatorBound
import NCG.Grand.DenseSourceStrongConvergence
import NCG.Grand.ResolventMoscoConverse

/-!
# The Grand-Tensor Mosco equivalence: the record-level bundle

Assembly for `thm:GT-Mosco` from the compiled varying-Hilbert Mosco library:
on the finite Hermitian regulator model (stage spaces `ℓ²` over finite index
sets, stage forms the squared graph energies of the stage operators, stage
resolvents the canonical shifted inverses of the positive-semidefinite stage
matrices), with the limit form the extended squared graph energy of a densely
defined closed operator and the limit resolvents its weak variational
solutions:

* `gt_mosco_resolvent_norm`: every stage resolvent obeys the uniform bound
  `‖(A_n+λ)^{-1}‖ ≤ 1/λ` — derived from the weak resolvent equation alone;
* `gt_mosco` — the record bundle:
  (Q1 → Q2) Grand-Tensor (cofinal) Mosco convergence of the forms gives
  strong convergence `J_n(A_n+λ)^{-1}J_n^* → (A_∞+λ)^{-1}` at **every**
  `λ > 0`; (Q2 → Q1) strong convergence at **one** shift, cofinally, recovers
  Mosco convergence; (Q1 → Q3) the embedded semigroups
  `J_n e^{-tA_n} J_n^*` converge strongly, uniformly on every compact
  positive-time set, to the canonical heat semigroup of any one limit
  resolvent;
* `gt_mosco_dense_family`: resolvent convergence may be tested on any dense
  family of primitive source words;
* `gt_mosco_failure_witness`: failure produces one dense source word, one
  positive discrepancy margin, and one cofinal subsequence.
-/

open Filter Set Topology Matrix NCG.VaryingHilbert NCG.VaryingHilbert.System
open scoped ComplexOrder ENNReal

noncomputable section

namespace NCG
namespace GTMosco

universe u v x

variable {iota : ℕ → Type u}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type x} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
variable {Fn : ℕ → Type x}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F] in
/-- The uniform stage resolvent bound `‖(A_n+λ)^{-1}‖ ≤ 1/λ`, derived from the
weak variational resolvent equation alone. -/
theorem gt_mosco_resolvent_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (Dm : Submodule ℂ E) (Am : Dm →ₗ[ℂ] F)
    (T : E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam)
    (heq : ∀ f : E, OperatorGraphResolventEquation Dm Am lam f (T f)) :
    ‖T‖ ≤ 1 / lam := by
  refine ennrealResolvent_opNorm_le_inv
    (ennrealOperatorGraphEnergy Dm Am) T lam hlam fun f => ?_
  have h := heq f
  have heuler := h.weakEuler ⟨T f, h.mem⟩
  rw [ennrealOperatorGraphEnergy_toReal Dm Am (T f) h.mem]
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ) (Am ⟨T f, h.mem⟩),
    ← norm_sq_eq_re_inner (𝕜 := ℂ) (T f)] at heuler
  exact heuler

variable (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))

set_option maxHeartbeats 1600000 in -- heavy unification across reindexed systems
/-- **The Grand-Tensor Mosco equivalence** (`thm:GT-Mosco`): on the finite
Hermitian regulator model, (Q1) cofinal Mosco convergence of the extended
graph energies gives (Q2) strong convergence of the embedded resolvents at
every positive shift; (Q2) at one shift, cofinally, recovers (Q1); and (Q1)
gives (Q3) strong convergence of the embedded semigroups to the canonical
heat semigroup, uniformly on every compact positive-time set. -/
theorem gt_mosco
    (G : ∀ n, Matrix (iota n) (iota n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (iota n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F) (hD : Dense (D : Set H))
    (R : ℝ → H →L[ℂ] H)
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (iota n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (hclosed : (operatorLinearPMap D A).IsClosed)
    (hdense : J.IsAsymptoticallyDense)
    (hrealInner : ∀ x y : H, inner ℝ x y = RCLike.re (inner ℂ x y)) :
    -- (Q1) → (Q2) at every positive shift
    (J.CofinalMoscoConverges
        (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
        (ennrealOperatorGraphEnergy D A) →
      ∀ lam, 0 < lam → J.StrongOperatorConverges J
        (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
          (G n) lam) (R lam)) ∧
    -- (Q2) at one positive shift, cofinally → (Q1)
    (∀ lam0, 0 < lam0 →
      (∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
        (J.reindex φ).StrongOperatorConverges (J.reindex φ)
          (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
            (G (φ n)) lam0) (R lam0)) →
      J.CofinalMoscoConverges
        (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
        (ennrealOperatorGraphEnergy D A)) ∧
    -- (Q1) → (Q3) uniformly on compact positive-time sets
    (J.CofinalMoscoConverges
        (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
        (ennrealOperatorGraphEnergy D A) →
      ∀ b, 0 < b → ∀ s : Set ℝ, IsCompact s → (∀ t ∈ s, 0 < t) →
        J.StrongOperatorConvergesUniformlyOn
          (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
            Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n)))
          (fun t ↦ operatorGraphResolventHeat (R b) b t) s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hmosco lam hlam
    exact J.operatorGraphMosco_strongResolvents_allPositive Dn An D A
      (fun lam n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) R hmosco hstageEquation hlimitEquation lam hlam
  · intro lam0 hlam0 hT0 φ hφ
    exact
      ennrealOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent_of_weakEquation
      (J.reindex φ) (fun n ↦ Dn (φ n)) (fun n ↦ An (φ n)) D A
      (fun lam n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G (φ n)) lam) R (IsAsymptoticallyDense.reindex J hdense φ hφ)
      lam0 hlam0 (hT0 φ hφ)
      (fun lam hlam n f ↦ hstageEquation lam hlam (φ n) f)
      hlimitEquation
      (lowerSemicontinuous_ennrealOperatorGraphEnergy_of_isClosed D A hclosed)
      hD hrealInner
  · intro hmosco b hb s hs hsPos
    exact
      StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_canonicalResolventHeat
      J G hG Dn An D A hD R hmosco hstageEquation hlimitEquation b hb s hs hsPos

omit [(n : ℕ) → DecidableEq (iota n)] [InnerProductSpace ℝ H]
  [IsScalarTower ℝ ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] in
/-- **The dense-family clause**: resolvent convergence may be tested on any
dense family of primitive source words, given the uniform resolvent bound. -/
theorem gt_mosco_dense_family
    (Tn : ∀ n, EuclideanSpace ℂ (iota n) →L[ℂ] EuclideanSpace ℂ (iota n))
    (T : H →L[ℂ] H) (Dset : Set H) (hDset : Dense Dset)
    (source : H → ∀ n, EuclideanSpace ℂ (iota n))
    (hsource : ∀ d ∈ Dset, J.StronglyConverges (source d) d)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖Tn n‖ ≤ C)
    (hconv : ∀ d ∈ Dset,
      J.StronglyConverges (fun n ↦ Tn n (source d n)) (T d)) :
    J.StrongOperatorConverges J Tn T :=
  J.strongOperatorConverges_of_dense_sources_of_uniform_opNorm J Tn T
    Dset hDset source hsource C hC hbound hconv

omit [(n : ℕ) → DecidableEq (iota n)] [InnerProductSpace ℝ H]
  [IsScalarTower ℝ ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] in
/-- **The failure witness**: failure of resolvent convergence is separated by
one dense source word, one positive discrepancy margin, and one cofinal
subsequence. -/
theorem gt_mosco_failure_witness
    (Tn : ∀ n, EuclideanSpace ℂ (iota n) →L[ℂ] EuclideanSpace ℂ (iota n))
    (T : H →L[ℂ] H) (Dset : Set H) (hDset : Dense Dset)
    (source : H → ∀ n, EuclideanSpace ℂ (iota n))
    (hsource : ∀ d ∈ Dset, J.StronglyConverges (source d) d)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖Tn n‖ ≤ C)
    (hfail : ¬ J.StrongOperatorConverges J Tn T) :
    ∃ d ∈ Dset, ∃ ε > 0, ∀ N, ∃ n ≥ N,
      ε ≤ dist (J.embedding n (Tn n (source d n))) (T d) := by
  refine J.denseSource_discrepancy_of_not_strongOperatorConverges J Tn T
    Dset hDset source hsource C hC ?_ hfail
  intro n x y
  calc dist (J.embedding n (Tn n x)) (J.embedding n (Tn n y))
      = ‖Tn n (x - y)‖ := by
        rw [dist_eq_norm, ← map_sub, LinearIsometry.norm_map, map_sub]
    _ ≤ ‖Tn n‖ * ‖x - y‖ := (Tn n).le_opNorm (x - y)
    _ ≤ C * ‖x - y‖ := by
        gcongr
        exact hbound n
    _ = C * dist (J.embedding n x) (J.embedding n y) := by
        congr 1
        rw [dist_eq_norm, ← map_sub, LinearIsometry.norm_map]

end GTMosco
end NCG
