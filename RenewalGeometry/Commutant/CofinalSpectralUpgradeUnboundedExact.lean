/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.JointCommutatorUnboundedLimitGapChain
import RenewalGeometry.Commutant.DerivedKernelCofinalDualityExact
import RenewalGeometry.OperatorLimits.ENNRealMoscoResolventConvergence

/-!
# Compact spectral upgrade and protected-kernel locking with an unbounded limiting form

Covers `cor:cofinal-spectral-upgrade` and `prop:protected-kernel-locking` of the
spacetime–gauge duality manuscript, replacing the earlier bounded-limit graph-screen packet
(whose hypotheses are contradictory, see `BoundedGraphScreenPacketFiniteDimensional.lean`).

The cutoff forms are the commutator energies `q_X(B) = Σ_j ‖[c_{j,X}, B]‖²_HS` on the finite
Hilbert–Schmidt screens, transported into a common carrier `ℋ` by isometries `J_X`.  The
limiting screened space is an arbitrary Hilbert space `H_∞` embedded isometrically by `J_∞`
(possibly a proper subspace of `ℋ`), with the paper's compatibility `P_X → P_∞ = J_∞ J_∞^*`
strongly, and (D1) is the transported Mosco convergence of `def:transported-mosco`
(`System.TransportedMoscoConverges`), exactly the hypothesis of the parent
`derivedKernelCofinalDuality_exact`.  The limiting form is the closed form `q_∞(v) = ‖A v‖²` of
a densely defined, possibly **unbounded**, operator `A : D →ₗ F` on `H_∞`, whose resolvent `R`
is given by the weak graph-resolvent equations.  Asymptotic form compactness is rendered, as in
`prop:compact-mosco-resolvent`, by a compact graph-screen tail for the cutoff graph resolvents.
The infinite-dimensionality hypothesis of the old packet is replaced by the corollary's own
hypothesis: the limiting space has a **nonzero complement** to `M_∞`.

* `protectedKernelLocking_exact` (`prop:protected-kernel-locking`).
* `cofinalSpectralUpgradeUnbounded_exact` (`cor:cofinal-spectral-upgrade`), assuming the
  hypotheses (D1)–(D3) of `thm:cofinal-duality` (proved: `derivedKernelCofinalDuality_exact`).
* `cofinalSpectralUpgradeUnbounded_nonvacuous`: the full hypothesis packet is satisfiable
  (constant cutoffs `c = diag(1,0)` on `2 × 2` matrices, where the commutant is a proper
  subspace).
* `CofinalMoscoConverges.transportedMoscoConverges_id` is only used to build the witness.
-/

open Complex Filter Set Topology Matrix
open scoped ENNReal

noncomputable section

namespace RenewalGeometry.VaryingHilbert

/-- The extended graph energy vanishes exactly on the graph kernel. -/
theorem ennrealOperatorGraphEnergy_eq_zero_iff_mem_operatorGraphKernel
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F) (x : E) :
    ennrealOperatorGraphEnergy D A x = 0 ↔ x ∈ operatorGraphKernel D A := by
  classical
  rw [mem_operatorGraphKernel_iff, ennrealOperatorGraphEnergy]
  by_cases hx : x ∈ D
  · rw [dif_pos hx, ENNReal.ofReal_eq_zero]
    constructor
    · intro h
      refine ⟨hx, ?_⟩
      have h2 : ‖A ⟨x, hx⟩‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
      exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
    · rintro ⟨_, h⟩
      simp [h]
  · rw [dif_neg hx]
    simp [hx]

namespace System

universe u v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ ℂ (Hn n)]

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [∀ n, InnerProductSpace ℝ (Hn n)]
  [∀ n, IsScalarTower ℝ ℂ (Hn n)] in
/-- Cofinal Mosco convergence on the common carrier is transported Mosco convergence
(`def:transported-mosco`) with the identity as limit embedding. -/
theorem CofinalMoscoConverges.transportedMoscoConverges_id
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : H → ℝ≥0∞}
    (hmosco : J.CofinalMoscoConverges q qlim) :
    J.TransportedMoscoConverges (LinearIsometry.id) q qlim where
  weak_liminf x B hx := ⟨B, rfl, (hmosco id tendsto_id).liminf_le x B hx⟩
  recovery A _ := (hmosco id tendsto_id).exists_recovery_energy_tendsto A

end System

end RenewalGeometry.VaryingHilbert

namespace RenewalGeometry.VaryingHilbert.System

universe u v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Hlim : Type w} [NormedAddCommGroup Hlim] [InnerProductSpace ℂ Hlim] [CompleteSpace Hlim]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Protected-kernel locking (`prop:protected-kernel-locking`).**  Let the cutoff commutator
forms `q_X(B) = Σ_j ‖[c_{j,X}, B]‖²_HS` converge in the transported Mosco sense
(`def:transported-mosco`) to the closed form `q_∞(v) = ‖A v‖²` of a densely defined operator
`A : D →ₗ F` on the limiting screened space `H_∞`, embedded isometrically by `J_∞` with
`P_X → P_∞ = J_∞ J_∞^*` strongly, and let the family be asymptotically compact (compact graph
screens).  Suppose each `M_X` is a subspace of `Ker 𝓛_X` of dimension `m = dim M_∞`, where
`Ker 𝓛_∞ = M_∞`, and that `λ_{m+1}(𝓛_∞)` exists (`M_∞ ≠ H_∞`).  Then for all late cutoffs
`Ker 𝓛_X = M_X`; the transported kernel projections converge in operator norm to
`J_∞ P_{M_∞} J_∞^*`; and `λ_{m+1}(𝓛_X) → γ_∞ > 0`, where `λ_{m+1}(𝓛_X)` is the attained least
positive eigenvalue of `𝓛_X` and `γ_∞ = λ_{m+1}(𝓛_∞)` is attained on some `v ∈ D ∩ M_∞^⊥`
(`‖A v‖² = γ_∞ ‖v‖²`, `R v = (γ_∞ + b)⁻¹ v`) and satisfies `γ_∞ ‖(I − P_{M_∞})v‖² ≤ ‖A v‖²` on
`D`. -/
theorem protectedKernelLocking_exact
    {d : ℕ → Type u} [∀ X, Fintype (d X)] {s : ℕ}
    (c : ∀ X, Fin s → Matrix (d X) (d X) ℂ)
    (J : System (K := ℂ) (H := H) (Hn := fun X ↦ EuclideanSpace ℂ (d X × d X)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun X ↦ WithLp 2
        (EuclideanSpace ℂ (d X × d X) × EuclideanSpace ℂ (Fin s × (d X × d X)))))
    (Jlim : Hlim →ₗᵢ[ℂ] H)
    (hcompat : ∀ g, Tendsto (fun X ↦ J.rangeProjection X g) atTop
      (𝓝 (transportedLimitOperator Jlim 1 g)))
    (D : Submodule ℂ Hlim) (A : D →ₗ[ℂ] F) (R : Hlim →L[ℂ] Hlim)
    (hmosco : J.TransportedMoscoConverges Jlim
      (fun X ↦ ennrealBoundedOperatorEnergy (RenewalGeometry.jointCommutatorCLM (c X)))
      (ennrealOperatorGraphEnergy D A))
    (hDdense : Dense (D : Set Hlim))
    (b : ℝ) (hb : 0 < b)
    (hlimitEquation : ∀ f : Hlim, OperatorGraphResolventEquation D A b f (R f))
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ k, IsCompactOperator (screen k))
    (htail : ∀ ε > 0, ∃ k, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun X ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d X × d X)))
        (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c X)))
        (RenewalGeometry.jointCommutatorResolventFamily c b X) b hb
        (RenewalGeometry.jointCommutatorResolventFamily_resolventEquation c b hb X)),
      ‖y - screen k y‖ < ε)
    (hfst : ∀ X y, J.embedding X y.fst = (L.embedding X y).fst)
    (M : ∀ X, Submodule ℂ (EuclideanSpace ℂ (d X × d X)))
    (hMker : ∀ X,
      M X ≤ LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap)
    (Mlim : Submodule ℂ Hlim) [Mlim.HasOrthogonalProjection]
    (hMlim : operatorGraphKernel D A = Mlim)
    (hMrank : ∀ X, Module.finrank ℂ (M X) = Module.finrank ℂ Mlim)
    (hcompl : Mlim ≠ ⊤) :
    FiniteDimensional ℂ Mlim ∧
      (∀ᶠ X in atTop,
        LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap = M X) ∧
      Tendsto (J.compressedOperator
          (fun X ↦ RenewalGeometry.jointCommutatorKernelProjection (c X)))
        atTop (𝓝 (transportedLimitOperator Jlim Mlim.starProjection)) ∧
      0 < RenewalGeometry.graphLimitComplementGap R Mlim b ∧
      Tendsto (fun X ↦ RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b) atTop
        (𝓝 (RenewalGeometry.graphLimitComplementGap R Mlim b)) ∧
      (∀ᶠ X in atTop,
        0 < RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b ∧
          Module.End.HasEigenvalue
            (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap
            ((RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b : ℝ) : ℂ) ∧
          ∀ ν : ℝ, 0 < ν →
            Module.End.HasEigenvalue
              (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap (ν : ℂ) →
              RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b ≤ ν) ∧
      (∃ v : Hlim, ∃ hv : v ∈ D, v ≠ 0 ∧ v ∈ Mlimᗮ ∧
        R v = (((RenewalGeometry.graphLimitComplementGap R Mlim b + b)⁻¹ : ℝ) : ℂ) • v ∧
        ‖A ⟨v, hv⟩‖ ^ 2 = RenewalGeometry.graphLimitComplementGap R Mlim b * ‖v‖ ^ 2) ∧
      (∀ v : Hlim, ∀ hv : v ∈ D,
        RenewalGeometry.graphLimitComplementGap R Mlim b *
            ‖v - Mlim.starProjection v‖ ^ 2 ≤ ‖A ⟨v, hv⟩‖ ^ 2) := by
  obtain ⟨hfin, hker, -, -, hproj, hpos, hgap, heig, hvec, hvar, -⟩ :=
    J.jointCommutator_unboundedLimitGapChain c L Jlim hcompat D A R hmosco hDdense b hb
      hlimitEquation screen hcompact htail hfst M (Eventually.of_forall hMker) Mlim hMlim
      (Eventually.of_forall hMrank) hcompl
  exact ⟨hfin, hker, hproj, hpos, hgap, heig, hvec, hvar⟩

/-- **Compact spectral upgrade (`cor:cofinal-spectral-upgrade`), unbounded limiting form on a
general limiting screened space.**  Assume the hypotheses of `thm:cofinal-duality` exactly as in
`derivedKernelCofinalDuality_exact`: (D1) transported Mosco convergence
(`def:transported-mosco`) of the cutoff commutator forms to the limiting form on `H_∞` embedded
isometrically by `J_∞` — here the closed form `q_∞(v) = ‖A v‖²` of a densely defined
`A : D →ₗ F` with weak resolvent `R` — with `P_X → P_∞ = J_∞ J_∞^*` strongly; (D2) protected
subspaces `M_X ⊆ Ker 𝓛_X` with orthonormal bases indexed by one finite type and a specified
`M_∞` with basis transport `η_X → 0`; (D3) a uniform late-cutoff gap `γ_* > 0`.  Assume in
addition asymptotic form compactness (compact graph screens) and a nonzero complement
`M_∞ ≠ H_∞`.  Then, besides the parent conclusions (`Ker 𝓛_X = M_X = C^*(c_X)'` late,
`Ker 𝓛_∞ = M_∞`):

* `eq:limit-gap`: `γ_∞ := λ_{m+1}(𝓛_∞) ≥ γ_* > 0`, `γ_∞` attained on an eigenvector in
  `D ∩ M_∞^⊥` and minimising the Rayleigh quotient on the complement;
* `eq:cofinal-norm-resolvent`: `‖J_X R_X J_X^* − J_∞ R J_∞^*‖ → 0`, `R` compact;
* `eq:cofinal-spectral-upgrade`: `λ_{m+1}(𝓛_X) → γ_∞` and `‖Π_X − Π_∞‖ → 0`, with
  `Π_∞ = J_∞ P_{M_∞} J_∞^*`;
* `eq:cofinal-coercivity`: for every `0 < γ_0 < γ_∞` and all late cutoffs
  `q_X(B) ≥ γ_0 ‖(I − P_{M_X})B‖²`. -/
theorem cofinalSpectralUpgradeUnbounded_exact
    {d : ℕ → Type u} [∀ X, Fintype (d X)] [∀ X, DecidableEq (d X)] {s : ℕ}
    (c : ∀ X, Fin s → Matrix (d X) (d X) ℂ)
    (hstar : ∀ X j, ∃ k, (c X j)ᴴ = c X k)
    (J : System (K := ℂ) (H := H) (Hn := fun X ↦ EuclideanSpace ℂ (d X × d X)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun X ↦ WithLp 2
        (EuclideanSpace ℂ (d X × d X) × EuclideanSpace ℂ (Fin s × (d X × d X)))))
    (Jlim : Hlim →ₗᵢ[ℂ] H)
    (hcompat : ∀ g, Tendsto (fun X ↦ J.rangeProjection X g) atTop
      (𝓝 (transportedLimitOperator Jlim 1 g)))
    (D : Submodule ℂ Hlim) (A : D →ₗ[ℂ] F) (R : Hlim →L[ℂ] Hlim)
    (hD1 : J.TransportedMoscoConverges Jlim
      (fun X ↦ ennrealBoundedOperatorEnergy (RenewalGeometry.jointCommutatorCLM (c X)))
      (ennrealOperatorGraphEnergy D A))
    (hDdense : Dense (D : Set Hlim))
    (b : ℝ) (hb : 0 < b)
    (hlimitEquation : ∀ f : Hlim, OperatorGraphResolventEquation D A b f (R f))
    {ι : Type*} [Fintype ι]
    (M : ∀ X, Submodule ℂ (EuclideanSpace ℂ (d X × d X)))
    (e : ∀ X, ι → EuclideanSpace ℂ (d X × d X)) (he : ∀ X, Orthonormal ℂ (e X))
    (hspan : ∀ X, Submodule.span ℂ (Set.range (e X)) = M X)
    (hMker : ∀ X,
      M X ≤ LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap)
    (Mlim : Submodule ℂ Hlim) [Mlim.HasOrthogonalProjection]
    (elim : ι → Hlim) (helim : Orthonormal ℂ elim)
    (hspanlim : Submodule.span ℂ (Set.range elim) = Mlim)
    (hη : Tendsto (J.basisTransportDefect e Jlim elim) atTop (𝓝 0))
    (γstar : ℝ) (hγ : 0 < γstar)
    (hD3 : ∀ᶠ X in atTop, ∀ B : EuclideanSpace ℂ (d X × d X),
      γstar * ‖B - (M X).starProjection B‖ ^ 2 ≤
        ‖RenewalGeometry.jointCommutatorCLM (c X) B‖ ^ 2)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ k, IsCompactOperator (screen k))
    (htail : ∀ ε > 0, ∃ k, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun X ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d X × d X)))
        (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c X)))
        (RenewalGeometry.jointCommutatorResolventFamily c b X) b hb
        (RenewalGeometry.jointCommutatorResolventFamily_resolventEquation c b hb X)),
      ‖y - screen k y‖ < ε)
    (hfst : ∀ X y, J.embedding X y.fst = (L.embedding X y).fst)
    (hcompl : Mlim ≠ ⊤) :
    (∀ᶠ X in atTop,
      LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap = M X ∧
        ∀ T : Matrix (d X) (d X) ℂ,
          T ∈ RenewalGeometry.matCommutant
              ((StarAlgebra.adjoin ℂ (Set.range (c X)) :
                StarSubalgebra ℂ (Matrix (d X) (d X) ℂ)) : Set (Matrix (d X) (d X) ℂ)) ↔
            RenewalGeometry.matrixL2 T ∈ M X) ∧
      operatorGraphKernel D A = Mlim ∧
      FiniteDimensional ℂ Mlim ∧ Module.finrank ℂ Mlim = Fintype.card ι ∧
      -- eq:limit-gap
      0 < γstar ∧ γstar ≤ RenewalGeometry.graphLimitComplementGap R Mlim b ∧
      (∃ v : Hlim, ∃ hv : v ∈ D, v ≠ 0 ∧ v ∈ Mlimᗮ ∧
        R v = (((RenewalGeometry.graphLimitComplementGap R Mlim b + b)⁻¹ : ℝ) : ℂ) • v ∧
        ‖A ⟨v, hv⟩‖ ^ 2 = RenewalGeometry.graphLimitComplementGap R Mlim b * ‖v‖ ^ 2) ∧
      (∀ v : Hlim, ∀ hv : v ∈ D,
        RenewalGeometry.graphLimitComplementGap R Mlim b *
            ‖v - Mlim.starProjection v‖ ^ 2 ≤ ‖A ⟨v, hv⟩‖ ^ 2) ∧
      -- eq:cofinal-norm-resolvent
      IsCompactOperator R ∧
      Tendsto (J.compressedOperator (RenewalGeometry.jointCommutatorResolventFamily c b))
        atTop (𝓝 (transportedLimitOperator Jlim R)) ∧
      -- eq:cofinal-spectral-upgrade
      Tendsto (fun X ↦ RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b) atTop
        (𝓝 (RenewalGeometry.graphLimitComplementGap R Mlim b)) ∧
      (∀ᶠ X in atTop,
        0 < RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b ∧
          Module.End.HasEigenvalue
            (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap
            ((RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b : ℝ) : ℂ) ∧
          ∀ ν : ℝ, 0 < ν →
            Module.End.HasEigenvalue
              (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap (ν : ℂ) →
              RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b ≤ ν) ∧
      Tendsto (J.compressedOperator
          (fun X ↦ RenewalGeometry.jointCommutatorKernelProjection (c X)))
        atTop (𝓝 (transportedLimitOperator Jlim Mlim.starProjection)) ∧
      -- eq:cofinal-coercivity
      (∀ γ0 : ℝ, 0 < γ0 → γ0 < RenewalGeometry.graphLimitComplementGap R Mlim b →
        ∀ᶠ X in atTop, ∀ B : EuclideanSpace ℂ (d X × d X),
          γ0 * ‖B - (M X).starProjection B‖ ^ 2 ≤
            ‖RenewalGeometry.jointCommutatorCLM (c X) B‖ ^ 2) := by
  -- the parent theorem
  obtain ⟨hcofinalKernel, hlimgap, hlimker⟩ :=
    derivedKernelCofinalDuality_exact c hstar J Jlim (ennrealOperatorGraphEnergy D A) hD1 M e he
      hspan hMker Mlim elim helim hspanlim hη γstar hγ hD3
  have hMlim : operatorGraphKernel D A = Mlim := by
    ext x
    rw [← ennrealOperatorGraphEnergy_eq_zero_iff_mem_operatorGraphKernel, hlimker x]
  have hrankX : ∀ X, Module.finrank ℂ (M X) = Fintype.card ι := by
    intro X
    rw [← hspan X]
    exact finrank_span_eq_card (he X).linearIndependent
  have hranklim : Module.finrank ℂ Mlim = Fintype.card ι := by
    rw [← hspanlim]
    exact finrank_span_eq_card helim.linearIndependent
  obtain ⟨hfin, -, hcompactR, hTconv, hproj, hpos, hgap, heig, hvec, hvar, hcoer⟩ :=
    J.jointCommutator_unboundedLimitGapChain c L Jlim hcompat D A R hD1 hDdense b hb
      hlimitEquation screen hcompact htail hfst M (Eventually.of_forall hMker) Mlim hMlim
      (Eventually.of_forall fun X ↦ (hrankX X).trans hranklim.symm) hcompl
  -- eq:limit-gap: test the parent's limiting gap on the attained eigenvector
  have hγle : γstar ≤ RenewalGeometry.graphLimitComplementGap R Mlim b := by
    obtain ⟨v, hv, hv0, hvperp, -, henergy⟩ := hvec
    have hPv : Mlim.starProjection v = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff (K := Mlim)).mpr hvperp
    have h := hlimgap v
    rw [hPv, sub_zero, ennrealOperatorGraphEnergy_of_mem D A hv,
      ENNReal.ofReal_le_ofReal_iff (sq_nonneg _), henergy] at h
    have hvpos : 0 < ‖v‖ ^ 2 := by positivity
    exact le_of_mul_le_mul_right h hvpos
  exact ⟨hcofinalKernel, hMlim, hfin, hranklim, hγ, hγle, hvec, hvar, hcompactR, hTconv,
    hgap, heig, hproj, fun γ0 _ hγ0 ↦ hcoer γ0 hγ0⟩

end RenewalGeometry.VaryingHilbert.System

/-! ### Non-vacuity witness for the hypothesis packets -/

namespace RenewalGeometry.VaryingHilbert.System.UnboundedSpectralUpgradeWitness

/-- Witness carrier: `2 × 2` matrices in Hilbert–Schmidt coordinates. -/
abbrev W := EuclideanSpace ℂ (Fin 2 × Fin 2)
/-- Witness target of the stacked commutator (one generator). -/
abbrev G := EuclideanSpace ℂ (Fin 1 × (Fin 2 × Fin 2))

/-- The single generator `diag(1, 0)`. -/
def gen : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ ↦ !![1, 0; 0, 0]

/-- Constant cutoffs embedded identically. -/
def Jw : System (K := ℂ) (H := W) (Hn := fun _ : ℕ ↦ EuclideanSpace ℂ (Fin 2 × Fin 2)) :=
  ⟨fun _ ↦ LinearIsometry.id⟩

/-- The graph-space system, embedded identically. -/
def Lw : System (K := ℂ) (H := WithLp 2 (W × G))
    (Hn := fun _ : ℕ ↦ WithLp 2 (EuclideanSpace ℂ (Fin 2 × Fin 2) ×
      EuclideanSpace ℂ (Fin 1 × (Fin 2 × Fin 2)))) :=
  ⟨fun _ ↦ LinearIsometry.id⟩

/-- The commutant `K = Ker ∂ = Ker 𝓛` of `gen`. -/
def Kw : Submodule ℂ W := LinearMap.ker (RenewalGeometry.jointCommutatorCLM gen).toLinearMap

/-- Weak convergence implies norm convergence in a finite-dimensional complex inner-product
space. -/
theorem tendsto_of_weak_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (x : ℕ → E) (xl : E)
    (h : ∀ y, Tendsto (fun n ↦ inner ℂ (x n) y) atTop (𝓝 (inner ℂ xl y))) :
    Tendsto x atTop (𝓝 xl) := by
  let b := stdOrthonormalBasis ℂ E
  have hx : x = fun n ↦ ∑ i, inner ℂ (b i) (x n) • b i := by
    funext n; exact (b.sum_repr' (x n)).symm
  rw [hx, ← b.sum_repr' xl]
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  have hi : Tendsto (fun n ↦ inner ℂ (b i) (x n)) atTop (𝓝 (inner ℂ (b i) xl)) := by
    have := (Complex.continuous_conj.tendsto _).comp (h (b i))
    simpa [Function.comp_def, inner_conj_symm] using this
  exact hi.smul_const _

theorem hmosco : Jw.CofinalMoscoConverges
    (fun _ ↦ ennrealOperatorGraphEnergy
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2 × Fin 2)))
      (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen)))
    (ennrealOperatorGraphEnergy (⊤ : Submodule ℂ W)
      (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen))) := by
  intro φ _
  have hcont := continuous_ennrealBoundedOperatorEnergy (RenewalGeometry.jointCommutatorCLM gen)
  constructor
  · intro x xlim hx
    have hxs : Tendsto (fun n ↦ (x n : W)) atTop (𝓝 xlim) :=
      tendsto_of_weak_of_finiteDimensional (fun n ↦ (x n : W)) xlim hx
    simp only [ennrealOperatorGraphEnergy_top]
    exact ((hcont.tendsto xlim).comp hxs).liminf_eq.ge
  · intro xlim
    refine ⟨fun _ ↦ xlim, tendsto_const_nhds, ?_⟩
    simp

/-- The witness limiting resolvent at shift `1`. -/
def Rw : W →L[ℂ] W := RenewalGeometry.jointCommutatorResolventAllShifts gen 1

theorem hlimitEquation : ∀ f : W,
    OperatorGraphResolventEquation (⊤ : Submodule ℂ W)
      (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen)) 1 f (Rw f) :=
  fun f ↦ RenewalGeometry.jointCommutatorResolventAllShifts_resolventEquation gen 1 one_pos f

/-- (D1) in the transported form, limiting space `W` embedded by the identity. -/
theorem hmoscoT : Jw.TransportedMoscoConverges (LinearIsometry.id)
    (fun _ ↦ ennrealBoundedOperatorEnergy (RenewalGeometry.jointCommutatorCLM gen))
    (ennrealOperatorGraphEnergy (⊤ : Submodule ℂ W)
      (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen))) := by
  have h := CofinalMoscoConverges.transportedMoscoConverges_id Jw hmosco
  simpa only [ennrealOperatorGraphEnergy_top] using h

theorem adjoint_id_apply (g : W) :
    ((LinearIsometry.id : W →ₗᵢ[ℂ] W).toContinuousLinearMap).adjoint g = g :=
  limitAdjoint_apply_embedding LinearIsometry.id g

/-- Compatibility `P_X → P_∞` (here all projections are the identity). -/
theorem hcompatW : ∀ g, Tendsto (fun X ↦ Jw.rangeProjection X g) atTop
    (𝓝 (transportedLimitOperator (LinearIsometry.id : W →ₗᵢ[ℂ] W) 1 g)) := by
  intro g
  have h1 : ∀ X, Jw.rangeProjection X g = g := fun X ↦ adjoint_id_apply g
  have h2 : transportedLimitOperator (LinearIsometry.id : W →ₗᵢ[ℂ] W) 1 g = g :=
    adjoint_id_apply g
  simp only [h1, h2]
  exact tendsto_const_nhds

theorem hDdense : Dense ((⊤ : Submodule ℂ W) : Set W) := by
  simp only [Submodule.top_coe]; exact dense_univ

/-- The identity screen (compact: everything is finite dimensional). -/
def screenW : ℕ → WithLp 2 (W × G) →L[ℂ] WithLp 2 (W × G) :=
  fun _ ↦ ContinuousLinearMap.id ℂ _

theorem hcompact : ∀ k, IsCompactOperator (screenW k) := by
  intro k
  exact ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩

theorem htail (a : ℝ) (ha : 0 < a) : ∀ ε > 0, ∃ k, ∀ y ∈ Lw.embeddedUnitBallOutputs
      (fun X ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2 × Fin 2)))
        (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM ((fun _ : ℕ ↦ gen) X)))
        (RenewalGeometry.jointCommutatorResolventFamily (fun _ : ℕ ↦ gen) a X) a ha
        (RenewalGeometry.jointCommutatorResolventFamily_resolventEquation
          (fun _ : ℕ ↦ gen) a ha X)),
      ‖y - screenW k y‖ < ε := by
  intro ε hε
  refine ⟨0, fun y _ ↦ ?_⟩
  simp [screenW, hε]

/-- `diag(1,0)` does not commute with the matrix unit `E₁₂`, so its commutant is proper. -/
theorem Kw_ne_top : Kw ≠ ⊤ := by
  intro htop
  have hmem : RenewalGeometry.matrixL2 (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈ Kw := by
    rw [htop]; exact Submodule.mem_top
  rw [Kw, RenewalGeometry.matrixL2_mem_jointCommutatorCLM_ker_iff] at hmem
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 1) (hmem 0)
  simp [gen, Matrix.mul_apply, Fin.sum_univ_two] at h

theorem hstar : ∀ (X : ℕ) (j : Fin 1), ∃ k, (((fun _ : ℕ ↦ gen) X) j)ᴴ = ((fun _ : ℕ ↦ gen) X) k := by
  intro X j
  refine ⟨j, ?_⟩
  ext i k
  fin_cases i <;> fin_cases k <;> simp [gen]

/-- Orthonormal basis vectors of the commutant. -/
def ew : Fin (Module.finrank ℂ Kw) → W := fun a ↦ ((stdOrthonormalBasis ℂ Kw a : Kw) : W)

theorem ew_orthonormal : Orthonormal ℂ ew :=
  (stdOrthonormalBasis ℂ Kw).orthonormal.comp_linearIsometry Kw.subtypeₗᵢ

theorem ew_span : Submodule.span ℂ (Set.range ew) = Kw := by
  have hrange : Set.range ew = Kw.subtype '' Set.range (stdOrthonormalBasis ℂ Kw) := by
    rw [← Set.range_comp]; rfl
  rw [hrange, Submodule.span_image, ← OrthonormalBasis.coe_toBasis,
    Module.Basis.span_eq, Submodule.map_subtype_top]

theorem Kw_le_ker : Kw ≤ LinearMap.ker (RenewalGeometry.commutantLaplacianCLM gen).toLinearMap := by
  rw [RenewalGeometry.ker_commutantLaplacianCLM]; exact le_rfl

theorem hη : Tendsto (Jw.basisTransportDefect (fun _ ↦ ew) (LinearIsometry.id) ew) atTop (𝓝 0) := by
  have h : Jw.basisTransportDefect (fun _ ↦ ew) (LinearIsometry.id) ew = fun _ ↦ 0 := by
    funext X
    simp [basisTransportDefect, Jw]
  rw [h]; exact tendsto_const_nhds

theorem hfst : ∀ (X : ℕ) (y : WithLp 2 (EuclideanSpace ℂ (Fin 2 × Fin 2) ×
    EuclideanSpace ℂ (Fin 1 × (Fin 2 × Fin 2)))),
    Jw.embedding X y.fst = (Lw.embedding X y).fst := fun _ _ ↦ rfl

theorem hMlim : operatorGraphKernel (⊤ : Submodule ℂ W)
    (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen)) = Kw :=
  operatorGraphKernel_top_boundedOperatorGraphMap _

/-- The witness cutoff gap is positive (obtained from the gap chain, which does not use (D3)). -/
theorem gap_pos : 0 < RenewalGeometry.jointCommutatorFirstPositiveGap gen 1 := by
  obtain ⟨-, -, -, -, -, -, -, heig, -, -, -⟩ :=
    Jw.jointCommutator_unboundedLimitGapChain (fun _ ↦ gen) Lw LinearIsometry.id hcompatW ⊤
      (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen)) Rw hmoscoT hDdense
      1 one_pos hlimitEquation screenW hcompact (htail 1 one_pos) hfst (fun _ ↦ Kw)
      (Eventually.of_forall fun _ ↦ Kw_le_ker) Kw hMlim (Eventually.of_forall fun _ ↦ rfl)
      Kw_ne_top
  obtain ⟨X, hX⟩ := heig.exists
  exact hX.1

theorem hD3 : ∀ᶠ X in atTop, ∀ B : EuclideanSpace ℂ (Fin 2 × Fin 2),
    RenewalGeometry.jointCommutatorFirstPositiveGap gen 1 *
        ‖B - ((fun _ : ℕ ↦ Kw) X).starProjection B‖ ^ 2 ≤
      ‖RenewalGeometry.jointCommutatorCLM ((fun _ : ℕ ↦ gen) X) B‖ ^ 2 :=
  Eventually.of_forall fun _ B ↦
    RenewalGeometry.jointCommutatorFirstPositiveGap_coercivity gen 1 one_pos B

/-- **Non-vacuity of the compact spectral upgrade packet.**  All hypotheses of
`cofinalSpectralUpgradeUnbounded_exact` (including (D1)–(D3) of `thm:cofinal-duality`, the
compact graph screens and the nonzero complement) hold for the constant cutoffs
`c_X = diag(1, 0)` on `2 × 2` matrices; the theorem then yields a positive limit gap. -/
theorem cofinalSpectralUpgradeUnbounded_nonvacuous :
    0 < RenewalGeometry.graphLimitComplementGap Rw Kw 1 := by
  obtain ⟨-, -, -, -, hγ, hγle, -⟩ :=
    cofinalSpectralUpgradeUnbounded_exact (fun _ ↦ gen) hstar Jw Lw LinearIsometry.id hcompatW ⊤
      (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen)) Rw hmoscoT hDdense
      1 one_pos hlimitEquation (fun _ ↦ Kw) (fun _ ↦ ew) (fun _ ↦ ew_orthonormal)
      (fun _ ↦ ew_span) (fun _ ↦ Kw_le_ker) Kw ew ew_orthonormal ew_span hη _ gap_pos hD3
      screenW hcompact (htail 1 one_pos) hfst Kw_ne_top
  exact hγ.trans_le hγle

/-- **Non-vacuity of the protected-kernel locking packet** (same witness). -/
theorem protectedKernelLocking_nonvacuous :
    Tendsto (fun X ↦ RenewalGeometry.jointCommutatorFirstPositiveGap ((fun _ : ℕ ↦ gen) X) 1)
      atTop (𝓝 (RenewalGeometry.graphLimitComplementGap Rw Kw 1)) := by
  obtain ⟨-, -, -, -, hgap, -⟩ :=
    protectedKernelLocking_exact (fun _ ↦ gen) Jw Lw LinearIsometry.id hcompatW ⊤
      (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen)) Rw hmoscoT hDdense
      1 one_pos hlimitEquation screenW hcompact (htail 1 one_pos) hfst (fun _ ↦ Kw)
      (fun _ ↦ Kw_le_ker) Kw hMlim (fun _ ↦ rfl) Kw_ne_top
  exact hgap

end RenewalGeometry.VaryingHilbert.System.UnboundedSpectralUpgradeWitness
