import NCG.Grand.CanonicalFiniteRateFibreRefresh
import NCG.Grand.FiniteRewardLumpabilityAndTiltedSelfEnergy
import NCG.Grand.SaturatedFiniteDiracGenerator
import NCG.Grand.SchurMoriEvolution

/-!
# Exact finite generator closure and Mori--Zwanzig alternative

This file collects the actual finite-dimensional ingredients of
`thm:accepted-generator-closure`: finite Krylov stabilization,
equivalence between commutation and the two quotient intertwinings,
semigroup descent, exact hidden-memory elimination, and the visible
Schur resolvent.
-/

open Matrix

namespace NCG
namespace AcceptedGeneratorClosure

/-- With `RC = I`, commutation of the decoded projection with the
generator is equivalent to the pair of forward and backward
intertwining identities for `A = RLC`. -/
theorem commutes_iff_two_sided_intertwining
    {U Z : Type*} [Fintype U] [Fintype Z]
    [DecidableEq U] [DecidableEq Z]
    (L : Matrix U U ℝ) (C : Matrix U Z ℝ) (R : Matrix Z U ℝ)
    (hRC : R * C = 1) :
    let E := C * R
    let A := R * L * C
    E * L = L * E ↔ L * C = C * A ∧ R * L = A * R := by
  dsimp
  constructor
  · intro h
    exact ⟨
      FiniteRewardLumpabilityAndTiltedSelfEnergy.fine_to_coarse_intertwining
        L C R hRC h,
      FiniteRewardLumpabilityAndTiltedSelfEnergy.coarse_to_fine_intertwining
        L C R hRC h⟩
  · rintro ⟨hC, hR⟩
    calc
      (C * R) * L = C * (R * L) := Matrix.mul_assoc _ _ _
      _ = C * ((R * L * C) * R) :=
        congrArg (fun X => C * X) hR
      _ = (C * (R * L * C)) * R := (Matrix.mul_assoc _ _ _).symm
      _ = (L * C) * R := congrArg (fun X => X * R) hC.symm
      _ = L * (C * R) := Matrix.mul_assoc _ _ _

/-- Exact continuous-time quotient dynamics obtained by
exponentiating both rectangular intertwinings. -/
theorem semigroup_two_sided_intertwining
    {U Z : Type*} [Fintype U] [Fintype Z]
    [DecidableEq U] [DecidableEq Z]
    (L : Matrix U U ℝ) (A : Matrix Z Z ℝ)
    (C : Matrix U Z ℝ) (R : Matrix Z U ℝ)
    (hC : L * C = C * A) (hR : R * L = A * R) (t : ℝ) :
    NormedSpace.exp (t • L) * C =
        C * NormedSpace.exp (t • A) ∧
      R * NormedSpace.exp (t • L) =
        NormedSpace.exp (t • A) * R := by
  constructor
  · exact CanonicalFiniteRateFibreRefresh.exp_intertwine_rect
      L A C hC t
  · have hRt : A * R = R * L := hR.symm
    exact (CanonicalFiniteRateFibreRefresh.exp_intertwine_rect
      A L R hRt t).symm

open scoped Matrix.Norms.Elementwise

/-- Complete algebraic/analytic closure alternative on a finite
carrier.  The first component is the genuine finite Krylov plateau;
the second and third are exact generator/semigroup descent; the
fourth and fifth are the Mori--Zwanzig memory and Schur-resolvent
identities supplied by the indicated hypotheses. -/
theorem accepted_generator_closure_and_mori
    {E U Z a b : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [Fintype U] [Fintype Z] [Fintype a] [Fintype b]
    [DecidableEq U] [DecidableEq Z] [DecidableEq a] [DecidableEq b]
    (K : ℕ → Submodule ℂ E) (T : E →ₗ[ℂ] E)
    (hmono : ∀ n, K n ≤ K (n + 1))
    (hforward : ∀ n, Submodule.map T (K n) ≤ K (n + 1))
    (L : Matrix U U ℝ) (Cq : Matrix U Z ℝ) (R : Matrix Z U ℝ)
    (hRC : R * Cq = 1)
    (A : Matrix a a ℂ) (B : Matrix a b ℂ) (Ch : Matrix b b ℂ)
    (Uf : ℝ → Matrix a a ℂ) (Vf : ℝ → Matrix b a ℂ)
    (hU : ∀ t : ℝ, HasDerivAt Uf (-A * Uf t - B * Vf t) t)
    (hVariation : ∀ t : ℝ,
      Vf t = -∫ s in (0 : ℝ)..t,
        (NormedSpace.exp ((s - t) • Ch) * Bᴴ * Uf s :
          Matrix b a ℂ))
    (hKernelIntegral : ∀ t : ℝ,
      B * (∫ s in (0 : ℝ)..t,
        (NormedSpace.exp ((s - t) • Ch) * Bᴴ * Uf s :
          Matrix b a ℂ))
      = ∫ s in (0 : ℝ)..t,
        (B * NormedSpace.exp ((s - t) • Ch) * Bᴴ) * Uf s)
    (z : ℂ) (Uhat : Matrix a a ℂ) (Vhat : Matrix b a ℂ)
    [Invertible (z • (1 : Matrix b b ℂ) + Ch)]
    (hTop : (z • (1 : Matrix a a ℂ) + A) * Uhat + B * Vhat = 1)
    (hBottom : Bᴴ * Uhat +
      (z • (1 : Matrix b b ℂ) + Ch) * Vhat = 0) :
    (∃ nStar,
      (∀ m, m < nStar → K m ≠ K (m + 1)) ∧
      K nStar = K (nStar + 1) ∧
      Submodule.map T (K nStar) ≤ K nStar)
    ∧ (((Cq * R) * L = L * (Cq * R)) ↔
      L * Cq = Cq * (R * L * Cq) ∧
      R * L = (R * L * Cq) * R)
    ∧ (∀ t : ℝ,
      ((Cq * R) * L = L * (Cq * R)) →
      NormedSpace.exp (t • L) * Cq =
          Cq * NormedSpace.exp (t • (R * L * Cq)) ∧
        R * NormedSpace.exp (t • L) =
          NormedSpace.exp (t • (R * L * Cq)) * R)
    ∧ (∀ t : ℝ, HasDerivAt Uf
      (-A * Uf t + ∫ s in (0 : ℝ)..t,
        (B * NormedSpace.exp ((s - t) • Ch) * Bᴴ) * Uf s) t)
    ∧ ((z • (1 : Matrix a a ℂ) + A
      - B * (z • (1 : Matrix b b ℂ) + Ch)⁻¹ * Bᴴ) * Uhat = 1) := by
  refine ⟨finiteKrylovChain_firstStabilization K T hmono hforward,
    commutes_iff_two_sided_intertwining L Cq R hRC, ?_, ?_, ?_⟩
  · intro t hcomm
    have hpair :=
      (commutes_iff_two_sided_intertwining L Cq R hRC).mp hcomm
    exact semigroup_two_sided_intertwining L (R * L * Cq)
      Cq R hpair.1 hpair.2 t
  · exact mori_volterra_equation A B Ch Uf Vf hU hVariation
      hKernelIntegral
  · exact mori_resolvent_equation A B Ch z Uhat Vhat hTop hBottom

end AcceptedGeneratorClosure
end NCG
