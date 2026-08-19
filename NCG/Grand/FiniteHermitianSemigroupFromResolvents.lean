/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianEulerRootResolventScaling
import NCG.Grand.FiniteHermitianEulerLimitUniformity

/-!
# Finite Hermitian semigroup convergence from shifted resolvents

At positive time, each finite Euler root is a scaled positive-shift resolvent.  Thus strong
convergence of the shifted resolvents automatically supplies every fixed-root hypothesis in the
finite Hermitian semigroup compiler.  The only remaining analytic input is convergence of the
Euler powers on the limit Hilbert space.
-/

open Filter Topology Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {ι : ℕ → Type u}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Strong convergence of every positive-shift finite Hermitian resolvent compiles directly into
fixed-time strong convergence of the literal matrix exponential semigroups. -/
theorem StrongOperatorConverges.of_finiteHermitianPositiveShiftResolvents
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (R : ℝ → H →L[ℂ] H)
    (hR : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (A n) lam) (R lam))
    (t : ℝ) (ht : 0 < t) (S : H →L[ℂ] H)
    (hEulerLimit : ∀ x : H,
      Tendsto
        (fun m ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        atTop (𝓝 (S x))) :
    J.StrongOperatorConverges J
      (fun n ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S := by
  apply StrongOperatorConverges.of_finiteHermitianEulerRoots
    J A hA t ht.le S
    (fun m ↦ (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
      R (((m + 1 : ℕ) : ℝ) / t))
  · intro m
    have hlam : 0 < ((m + 1 : ℕ) : ℝ) / t := by positivity
    have hscaled := NCG.VaryingHilbert.StrongOperatorConverges.smul J
      (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ))
      (hR (((m + 1 : ℕ) : ℝ) / t) hlam)
    simpa only [NCG.ImplicitEuler.finiteHermitianEulerRootOperator_eq_smul_shiftedResolvent
      (A := A _) (hA := hA _) (t := t) (m := m) ht] using hscaled
  · exact hEulerLimit


/-- Uniform-on-compact-time version on sets of strictly positive times.  Positive-shift
resolvent convergence supplies every fixed Euler root; only cutoff equicontinuity and convergence
of the limit Euler scheme remain explicit. -/
theorem StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (R : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] H)
    (hR : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (A n) lam) (R lam))
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hfixedEq : ∀ m, ∀ (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H),
      J.StronglyConverges x xlim →
        EquicontinuousOn
          (fun n t ↦ J.embedding n
            (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
              (A n) t (m + 1) (x n))) s)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        (fun t ↦ S t x) atTop s) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S s := by
  apply StrongOperatorConvergesUniformlyOn.of_finiteHermitianEulerRoots
    J A hA S
    (fun m t ↦ (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
      R (((m + 1 : ℕ) : ℝ) / t)) s hs
  · intro t ht
    exact (hsPos t ht).le
  · intro m t ht
    have htPos := hsPos t ht
    have hlam : 0 < ((m + 1 : ℕ) : ℝ) / t := by positivity
    have hscaled := NCG.VaryingHilbert.StrongOperatorConverges.smul J
      (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ))
      (hR (((m + 1 : ℕ) : ℝ) / t) hlam)
    simpa only [NCG.ImplicitEuler.finiteHermitianEulerRootOperator_eq_smul_shiftedResolvent
      (A := A _) (hA := hA _) (t := t) (m := m) htPos] using hscaled
  · exact hfixedEq
  · exact hEulerLimit


/-- On compact sets of strictly positive times, cutoff equicontinuity is automatic: fixed Euler
orders have a dimension- and spectrum-independent Lipschitz bound.  Thus only positive-shift
resolvent convergence and the genuinely limit-space Euler scheme remain as inputs. -/
theorem
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents_autoEquicontinuity
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (R : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] H)
    (hR : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (A n) lam) (R lam))
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        (fun t ↦ S t x) atTop s) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S s := by
  apply StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents
    J A hA R S hR s hs hsPos
  · intro m x xlim hx
    exact equicontinuousOn_finiteHermitianEulerResolventOperator
      J A hA (m + 1) (Nat.succ_pos m) s hs hsPos x xlim hx
  · exact hEulerLimit

/-- On a positive compact time set, pointwise convergence of the limit Euler scheme is enough.
The order-uniform cutoff Lipschitz estimate transfers through asymptotic density and Ascoli
supplies the formerly explicit uniform-in-time limit. -/
theorem
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents_pointwiseEuler
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (R : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] H)
    (hR : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (A n) lam) (R lam))
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hdense : J.IsAsymptoticallyDense)
    (hEulerLimit : ∀ x : H, ∀ t ∈ s,
      Tendsto
        (fun m ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
        atTop (𝓝 (S t x))) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S s := by
  let Q : ℕ → ℝ → H →L[ℂ] H := fun m t ↦
    ((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
      R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)
  have hQ : ∀ m, ∀ t ∈ s,
      J.StrongOperatorConverges J
        (fun n ↦ NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A n) t (m + 1)) (Q m t) := by
    intro m t ht
    have htPos := hsPos t ht
    have hlam : 0 < ((m + 1 : ℕ) : ℝ) / t := by positivity
    have hscaled := NCG.VaryingHilbert.StrongOperatorConverges.smul J
      (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ))
      (hR (((m + 1 : ℕ) : ℝ) / t) hlam)
    have hroot :
        J.StrongOperatorConverges J
          (fun n ↦ NCG.ImplicitEuler.finiteHermitianEulerRootOperator (A n) t m)
          (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ) •
            R (((m + 1 : ℕ) : ℝ) / t)) := by
      simpa only [NCG.ImplicitEuler.finiteHermitianEulerRootOperator_eq_smul_shiftedResolvent
        (A := A _) (hA := hA _) (t := t) (m := m) htPos] using hscaled
    simpa only [Q,
      NCG.ImplicitEuler.finiteHermitianEulerResolventOperator_succ_eq_root_pow] using
      NCG.VaryingHilbert.StrongOperatorConverges.pow J hroot (m + 1)
  have hUniform := tendstoUniformlyOn_limit_finiteHermitianEulerPowers_of_pointwise
    J A hA Q S s hs hsPos hdense hQ hEulerLimit
  exact
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents_autoEquicontinuity
      J A hA R S hR s hs hsPos hUniform
/-- Uniform-on-compact-time version allowing time zero.  At zero the Euler root and its limit
counterpart are both the identity; at positive times the root is the scaled shifted resolvent. -/
theorem StrongOperatorConvergesUniformlyOn.of_finiteHermitianPositiveShiftResolvents_nonnegative
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (R : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] H)
    (hR : ∀ lam, 0 < lam → J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (A n) lam) (R lam))
    (s : Set ℝ) (hs : IsCompact s) (hsNonneg : ∀ t ∈ s, 0 ≤ t)
    (hfixedEq : ∀ m, ∀ (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H),
      J.StronglyConverges x xlim →
        EquicontinuousOn
          (fun n t ↦ J.embedding n
            (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
              (A n) t (m + 1) (x n))) s)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦
          (((if t = 0 then ContinuousLinearMap.id ℂ H
            else (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ) •
              R (((m + 1 : ℕ) : ℝ) / t))) ^ (m + 1)) x))
        (fun t ↦ S t x) atTop s) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S s := by
  apply StrongOperatorConvergesUniformlyOn.of_finiteHermitianEulerRoots
    J A hA S
    (fun m t ↦ if t = 0 then ContinuousLinearMap.id ℂ H
      else (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ) •
        R (((m + 1 : ℕ) : ℝ) / t))) s hs hsNonneg
  · intro m t ht
    by_cases ht0 : t = 0
    · subst t
      intro x xlim hx
      simpa [NCG.ImplicitEuler.finiteHermitianEulerRootOperator,
        NCG.VaryingHilbert.System.StrongOperatorConverges] using hx
    · have htPos : 0 < t := lt_of_le_of_ne (hsNonneg t ht) (Ne.symm ht0)
      have hlam : 0 < ((m + 1 : ℕ) : ℝ) / t := by positivity
      have hscaled := NCG.VaryingHilbert.StrongOperatorConverges.smul J
        (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ))
        (hR (((m + 1 : ℕ) : ℝ) / t) hlam)
      simpa only [ht0, if_false,
        NCG.ImplicitEuler.finiteHermitianEulerRootOperator_eq_smul_shiftedResolvent
          (A := A _) (hA := hA _) (t := t) (m := m) htPos] using hscaled
  · exact hfixedEq
  · exact hEulerLimit
end NCG.VaryingHilbert.System
