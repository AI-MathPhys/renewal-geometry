import NCG.Upstream.SemigroupLimit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Krylov span equals the continuous exponential-orbit span

On a finite-dimensional complex carrier, the span of the powers
`A^n x` is exactly the span of `exp(tA)x`.  One inclusion follows
from the exponential series and closedness of finite-dimensional
subspaces.  For the converse, differentiating the exponential orbit
shows that its closed span is invariant under `A`.
-/

open Set

namespace NCG
namespace AcceptedKrylovOrbitSpan

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

def powerSpan (A : V →L[ℂ] V) (x : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun n : ℕ => (A ^ n) x)

def orbitSpan (A : V →L[ℂ] V) (x : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun t : ℂ => NormedSpace.exp (t • A) x)

theorem exp_smul_apply_mem_powerSpan
    (A : V →L[ℂ] V) (x : V) (t : ℂ) :
    NormedSpace.exp (t • A) x ∈ powerSpan A x := by
  rw [Upstream.exp_apply_tsum]
  apply tsum_mem (powerSpan A x).closed_of_finiteDimensional
  intro n
  have hp : ((t • A) ^ n) x = t ^ n • (A ^ n) x := by
    rw [smul_pow]
    exact ContinuousLinearMap.smul_apply _ _ _
  rw [hp, smul_smul]
  exact (powerSpan A x).smul_mem _
    (Submodule.subset_span ⟨n, rfl⟩)

theorem orbitSpan_le_powerSpan (A : V →L[ℂ] V) (x : V) :
    orbitSpan A x ≤ powerSpan A x := by
  apply Submodule.span_le.mpr
  rintro y ⟨t, rfl⟩
  exact exp_smul_apply_mem_powerSpan A x t

private theorem orbit_deriv_mem
    (A : V →L[ℂ] V) (x : V) (t : ℂ) :
    deriv (fun u : ℂ => NormedSpace.exp (u • A) x) t ∈
      orbitSpan A x := by
  have hrange :=
    range_deriv_subset_closure_span_image
      (fun u : ℂ => NormedSpace.exp (u • A) x)
      (dense_univ : Dense (Set.univ : Set ℂ))
  have hmem := hrange ⟨t, rfl⟩
  have horbitClosed : IsClosed (orbitSpan A x : Set V) :=
    (orbitSpan A x).closed_of_finiteDimensional
  rw [show Submodule.span ℂ
      ((fun u : ℂ => NormedSpace.exp (u • A) x) '' Set.univ) =
        orbitSpan A x by
      apply congrArg (Submodule.span ℂ)
      ext y
      simp [orbitSpan]]
    at hmem
  rw [horbitClosed.closure_eq] at hmem
  exact hmem

private theorem generator_maps_orbit_to_span
    (A : V →L[ℂ] V) (x : V) (t : ℂ) :
    A (NormedSpace.exp (t • A) x) ∈ orbitSpan A x := by
  have hdOp := hasDerivAt_exp_smul_const A t
  have hd := hdOp.clm_apply (hasDerivAt_const (x := t) x)
  have hformula :
      deriv (fun u : ℂ => NormedSpace.exp (u • A) x) t =
        (NormedSpace.exp (t • A) * A) x := by
    simpa using hd.deriv
  have hcomm : NormedSpace.exp (t • A) * A =
      A * NormedSpace.exp (t • A) := by
    exact (Commute.exp_left (Commute.smul_left (Commute.refl A) t)).eq
  have hm := orbit_deriv_mem A x t
  rw [hformula, hcomm] at hm
  exact hm

theorem generator_maps_orbitSpan
    (A : V →L[ℂ] V) (x : V) :
    Submodule.map A.toLinearMap (orbitSpan A x) ≤ orbitSpan A x := by
  rw [orbitSpan, Submodule.map_span_le]
  rintro y ⟨t, rfl⟩
  exact generator_maps_orbit_to_span A x t

theorem power_apply_mem_orbitSpan
    (A : V →L[ℂ] V) (x : V) :
    ∀ n : ℕ, (A ^ n) x ∈ orbitSpan A x := by
  intro n
  induction n with
  | zero =>
      have h0 : NormedSpace.exp ((0 : ℂ) • A) x = x := by simp
      change x ∈ orbitSpan A x
      rw [← h0]
      exact Submodule.subset_span ⟨0, by simp⟩
  | succ n ih =>
      rw [pow_succ']
      change A ((A ^ n) x) ∈ orbitSpan A x
      exact generator_maps_orbitSpan A x ⟨(A ^ n) x, ih, rfl⟩

theorem powerSpan_le_orbitSpan (A : V →L[ℂ] V) (x : V) :
    powerSpan A x ≤ orbitSpan A x := by
  apply Submodule.span_le.mpr
  rintro y ⟨n, rfl⟩
  exact power_apply_mem_orbitSpan A x n

/-- The boxed generator-native identity:
`span {A^n x} = span {exp(tA)x}`. -/
theorem powerSpan_eq_orbitSpan (A : V →L[ℂ] V) (x : V) :
    powerSpan A x = orbitSpan A x :=
  le_antisymm (powerSpan_le_orbitSpan A x)
    (orbitSpan_le_powerSpan A x)

end AcceptedKrylovOrbitSpan
end NCG
