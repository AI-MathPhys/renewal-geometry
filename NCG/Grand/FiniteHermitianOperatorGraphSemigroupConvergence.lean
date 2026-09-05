/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphMoscoResolventConvergence
import NCG.Grand.FiniteHermitianSemigroupFromResolvents
import NCG.Grand.OperatorGraphResolventBound
import NCG.Grand.DenseOperatorPointwiseConvergence

/-!
# Finite Hermitian semigroups from Mosco-convergent operator graphs

This compiler joins the graph-form and finite spectral-calculus layers.  Cofinal Mosco
convergence and weak Euler equations imply convergence of every shifted resolvent.  Exact
Euler-root scaling then converts those resolvents into convergence of the literal finite matrix
exponentials at each positive time.
-/

open Filter Set Topology Matrix
open scoped ComplexOrder ENNReal Norms.L2Operator

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v x z

variable {ι : ℕ → Type u}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type x} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
variable {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- Weak graph equations for the literal shifted inverses of positive-semidefinite Hermitian
cutoff matrices, together with cofinal Mosco convergence, imply fixed-time convergence of their
literal exponential semigroups.  Only the limit-space Euler-power convergence remains explicit. -/
theorem StrongOperatorConverges.of_finiteHermitianOperatorGraphMosco
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (G : ∀ n, Matrix (ι n) (ι n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (ι n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (ι n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (t : ℝ) (ht : 0 < t) (S : H →L[ℂ] H)
    (hEulerLimit : ∀ x : H,
      Tendsto
        (fun m ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        atTop (𝓝 (S x))) :
    J.StrongOperatorConverges J
      (fun n ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (G n))) S := by
  have hresolvents : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) (R lam) :=
    J.operatorGraphMosco_strongResolvents_allPositive
      Dn An D A
      (fun lam n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) R hmosco hstageEquation hlimitEquation
  exact StrongOperatorConverges.of_finiteHermitianPositiveShiftResolvents
    J G hG R hresolvents t ht S hEulerLimit


/-- Uniform-on-compact-positive-time graph-form compiler.  The graph Mosco and weak Euler data
supply all shifted-resolvent convergence, so the only remaining inputs are cutoff
equicontinuity and the limit Euler scheme. -/
theorem StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (G : ∀ n, Matrix (ι n) (ι n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (ι n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (ι n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (S : ℝ → H →L[ℂ] H)
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hfixedEq : ∀ m,
      ∀ (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H),
      J.StronglyConverges x xlim →
        EquicontinuousOn
          (fun n t ↦ J.embedding n
            (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
              (G n) t (m + 1) (x n))) s)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        (fun t ↦ S t x) atTop s) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (G n))) S s := by
  have hresolvents : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) (R lam) :=
    J.operatorGraphMosco_strongResolvents_allPositive
      Dn An D A
      (fun lam n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) R hmosco hstageEquation hlimitEquation
  exact StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents
    J G hG R S hresolvents s hs hsPos hfixedEq hEulerLimit

/-- Positive-time graph-Mosco semigroup convergence with cutoff equicontinuity discharged by the
uniform fixed-order Euler estimate.  The sole remaining semigroup-specific input is convergence
of the Euler scheme on the limit Hilbert space. -/
theorem
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_automaticEquicontinuity
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (G : ∀ n, Matrix (ι n) (ι n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (ι n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (ι n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (S : ℝ → H →L[ℂ] H)
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        (fun t ↦ S t x) atTop s) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (G n))) S s := by
  apply StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco
    J G hG Dn An D A R hmosco hstageEquation hlimitEquation S s hs hsPos
  · intro m x xlim hx
    exact equicontinuousOn_finiteHermitianEulerResolventOperator
      J G hG (m + 1) (Nat.succ_pos m) s hs hsPos x xlim hx
  · exact hEulerLimit

/-- Positive-time graph-Mosco semigroup convergence now needs only pointwise convergence of the
limit Euler formula.  The graph equations supply all shifted resolvents, and the order-uniform
cutoff estimate plus asymptotic density upgrades the limit Euler convergence uniformly in time. -/
theorem
StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_pointwiseEuler
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (G : ∀ n, Matrix (ι n) (ι n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (ι n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (ι n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (S : ℝ → H →L[ℂ] H)
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hEulerLimit : ∀ x : H, ∀ t ∈ s,
      Tendsto
        (fun m ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        atTop (𝓝 (S t x))) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (G n))) S s := by
  have hresolvents : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) (R lam) :=
    J.operatorGraphMosco_strongResolvents_allPositive
      Dn An D A
      (fun lam n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) R hmosco hstageEquation hlimitEquation
  have hdense : J.IsAsymptoticallyDense :=
    (hmosco id tendsto_id).asymptoticallyDense
  exact
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents_pointwiseEuler
      J G hG R S hresolvents s hs hsPos hdense hEulerLimit
/-- It is enough to verify the limit Euler formula on any dense core.  The weak graph equation
makes every scaled resolvent, hence every Euler power, a contraction; the dense-operator extension
gives pointwise convergence for all vectors, after which the positive-time Ascoli compiler gives
uniform semigroup convergence. -/
theorem
StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_denseEulerCore
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (G : ∀ n, Matrix (ι n) (ι n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (ι n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (ι n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (S : ℝ → H →L[ℂ] H)
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (EulerCore : Set H) (hEulerCoreDense : Dense EulerCore)
    (hEulerCore : ∀ d ∈ EulerCore, ∀ t ∈ s,
      Tendsto
        (fun m ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) d)
        atTop (𝓝 (S t d))) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (G n))) S s := by
  have hEulerLimit : ∀ x : H, ∀ t ∈ s,
      Tendsto
        (fun m ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        atTop (𝓝 (S t x)) := by
    intro x t ht
    have htPos := hsPos t ht
    let Q : ℕ → H →L[ℂ] H := fun m ↦
      ((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
        R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)
    have hQbound : ∀ m, ‖Q m‖ ≤ 1 := by
      intro m
      let lam : ℝ := ((m + 1 : ℕ) : ℝ) / t
      have hlam : 0 < lam := by
        exact div_pos (by positivity) htPos
      have hroot : ‖((lam : ℂ) • R lam)‖ ≤ 1 :=
        norm_smul_operatorGraphResolvent_le_one
          D A (R lam) lam hlam (hlimitEquation lam hlam)
      change ‖((lam : ℂ) • R lam) ^ (m + 1)‖ ≤ 1
      by_cases hH : Nontrivial H
      · letI := hH
        calc
          ‖((lam : ℂ) • R lam) ^ (m + 1)‖
              ≤ ‖(lam : ℂ) • R lam‖ ^ (m + 1) := norm_pow_le _ _
          _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hroot
      · haveI : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH
        simp
    have hall := NCG.tendsto_apply_of_dense_of_uniform_opNorm
      Q (S t) EulerCore hEulerCoreDense 1 zero_le_one hQbound
      (fun d hd ↦ by simpa [Q] using hEulerCore d hd t ht)
    simpa [Q] using hall x
  exact
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_pointwiseEuler
      J G hG Dn An D A R hmosco hstageEquation hlimitEquation S s hs hsPos hEulerLimit
/-- Uniform graph-form semigroup convergence on compact sets of nonnegative times, including
time zero through the identity Euler root. -/
theorem StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_nonnegative
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (G : ∀ n, Matrix (ι n) (ι n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (ι n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (ι n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (S : ℝ → H →L[ℂ] H)
    (s : Set ℝ) (hs : IsCompact s) (hsNonneg : ∀ t ∈ s, 0 ≤ t)
    (hfixedEq : ∀ m,
      ∀ (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H),
      J.StronglyConverges x xlim →
        EquicontinuousOn
          (fun n t ↦ J.embedding n
            (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
              (G n) t (m + 1) (x n))) s)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦
          (((if t = 0 then ContinuousLinearMap.id ℂ H
            else (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ) •
              R (((m + 1 : ℕ) : ℝ) / t))) ^ (m + 1)) x))
        (fun t ↦ S t x) atTop s) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (G n))) S s := by
  have hresolvents : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) (R lam) :=
    J.operatorGraphMosco_strongResolvents_allPositive
      Dn An D A
      (fun lam n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam) R hmosco hstageEquation hlimitEquation
  exact
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents_nonnegative
      J G hG R S hresolvents s hs hsNonneg hfixedEq hEulerLimit
end NCG.VaryingHilbert.System
