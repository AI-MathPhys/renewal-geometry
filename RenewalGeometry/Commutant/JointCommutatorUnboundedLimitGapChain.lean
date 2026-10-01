/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.PositiveComplementCoercivity
import RenewalGeometry.OperatorLimits.OperatorGraphResolventDenseRange
import RenewalGeometry.OperatorLimits.OperatorGraphResolventBound
import RenewalGeometry.OperatorLimits.OperatorGraphResolventEigenspace
import RenewalGeometry.OperatorLimits.OperatorGraphResolventPositivity
import RenewalGeometry.OperatorLimits.ContourResolventBounds
import RenewalGeometry.OperatorLimits.IdempotentRangeOrthogonalization
import RenewalGeometry.OperatorLimits.CircleRieszProjectionEigenvector
import RenewalGeometry.OperatorLimits.CompressedOperatorNormConvergence
import RenewalGeometry.OperatorLimits.VaryingHilbertFiniteStageCompression
import RenewalGeometry.OperatorLimits.VaryingHilbertFiniteStageNorm
import RenewalGeometry.OperatorLimits.TransportedMoscoStrongResolventConvergence
import RenewalGeometry.OperatorLimits.CompactSymmetricRieszEigenspace
import RenewalGeometry.OperatorLimits.RieszProjectionStability
import RenewalGeometry.OperatorLimits.NearbyProjectionRankStability
import RenewalGeometry.OperatorLimits.OperatorGraphResolventGraphScreen
import RenewalGeometry.Commutant.JointCommutatorResolventFamily
import RenewalGeometry.Commutant.JointCommutatorFirstPositiveEigenvalue
import RenewalGeometry.Commutant.JointCommutatorCompressedResolventKernel

/-!
# The compact spectral gap chain for joint-commutator cutoffs with an unbounded limit

Reusable gap chain behind `cor:cofinal-spectral-upgrade` and `prop:protected-kernel-locking` of
the spacetime–gauge duality manuscript.  The cutoff forms are the finite commutator energies
`q_X(B) = ‖∂_X B‖² = Σ_j ‖[c_{j,X}, B]‖²_HS`; the limit is the **unbounded** closed form
`q_∞(v) = ‖A v‖²` of a densely defined operator `A : D →ₗ F` on a limiting Hilbert space
`H_∞` embedded isometrically into the common carrier by `J_∞`, with resolvent `R` given by the
weak graph-resolvent equations (no boundedness of `A` is assumed, so the packet is compatible
with a compact limit resolvent on an infinite-dimensional space).  Convergence is transported
Mosco convergence (`def:transported-mosco`) with `P_X → P_∞` strongly; norm-resolvent
convergence comes from `TransportedMoscoStrongResolventConvergence.lean`.  The infinite-dimensionality hypothesis of the earlier bounded-limit packet is
replaced by a **nonzero complement** `M_∞ ≠ ⊤` of the limiting kernel.

* `RenewalGeometry.jointCommutatorFirstPositiveGap c b` is `λ_{m+1}(𝓛)` of a finite
  commutant Laplacian, read off the complement-compressed shift-`b` resolvent;
  `jointCommutatorFirstPositiveGap_coercivity` proves the **finite-cutoff coercivity**
  `q(B) ≥ λ_{m+1}(𝓛) ‖(I − P_{Ker 𝓛})B‖²` (the spectral-theorem estimate), and
  `jointCommutatorFirstPositiveGap_isLeastPositiveEigenvalue` identifies a positive value as the
  attained least positive eigenvalue.
* `RenewalGeometry.graphLimitComplementGap R M b` is the limiting complement gap
  `‖(1 − P_M) R (1 − P_M)‖⁻¹ − b`.
* `System.jointCommutator_unboundedLimitGapChain`: under transported Mosco convergence,
  compact graph screens (asymptotic form compactness), protected subspaces `M_X ⊆ Ker 𝓛_X` of
  the limiting kernel dimension and a nonzero complement: eventually `Ker 𝓛_X = M_X`; the
  transported resolvents converge in norm to `J_∞ R J_∞^*`; the transported kernel projections
  converge in norm to `J_∞ P_{M_∞} J_∞^*`; the limit gap `γ_∞` is positive, is attained on an eigenvector in
  `D ∩ M_∞^⊥` with `‖A v‖² = γ_∞ ‖v‖²` and minimises the Rayleigh quotient on the complement
  (`γ_∞ ‖(I − P)v‖² ≤ ‖A v‖²` on `D`), i.e. `γ_∞ = λ_{m+1}(𝓛_∞)`; `λ_{m+1}(𝓛_X) → γ_∞`; and for
  every `γ_0 < γ_∞`, `q_X(B) ≥ γ_0 ‖(I − P_{M_X})B‖²` at all late cutoffs.
-/

open Complex Filter Set Topology
open scoped ENNReal

noncomputable section

namespace RenewalGeometry

universe u

/-- `λ_{m+1}(𝓛)` of the finite commutant Laplacian `𝓛 = ∂†∂` of a generator family, read off
the complement-compressed resolvent at shift `b`:
`‖(1 − P_{Ker}) (𝓛 + b)⁻¹ (1 − P_{Ker})‖⁻¹ − b`. -/
def jointCommutatorFirstPositiveGap {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (b : ℝ) : ℝ :=
  ‖SpectralGap.complementCompression (jointCommutatorResolventAllShifts c b)
    (jointCommutatorKernelProjection c)‖⁻¹ - b

theorem jointCommutatorResolventAllShifts_of_pos {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (b : ℝ) (hb : 0 < b) :
    jointCommutatorResolventAllShifts c b = jointCommutatorResolvent c b hb := by
  rw [jointCommutatorResolventAllShifts, dif_pos hb]

/-- `Re ⟨𝓛 B, B⟩ = ‖∂ B‖²` for the commutant Laplacian. -/
theorem re_inner_commutantLaplacianCLM {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (B : EuclideanSpace ℂ (n × n)) :
    (inner ℂ (commutantLaplacianCLM c B) B).re = ‖jointCommutatorCLM c B‖ ^ 2 := by
  rw [commutantLaplacianCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

/-- **Finite-cutoff coercivity** (the spectral-theorem estimate): for every `B`,
`λ_{m+1}(𝓛) ‖B − P_{Ker 𝓛} B‖² ≤ ‖∂ B‖² = q(B)`. -/
theorem jointCommutatorFirstPositiveGap_coercivity {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (b : ℝ) (hb : 0 < b) (B : EuclideanSpace ℂ (n × n)) :
    jointCommutatorFirstPositiveGap c b * ‖B - jointCommutatorKernelProjection c B‖ ^ 2 ≤
      ‖jointCommutatorCLM c B‖ ^ 2 := by
  have h := SpectralGap.complementCompression_coercivity (commutantLaplacianCLM c)
    (jointCommutatorResolvent c b hb) (jointCommutatorKernelProjection c) b
    (commutantLaplacianCLM_isPositive c)
    (VaryingHilbert.operatorGraphResolvent_isPositive
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (n × n)))
      (VaryingHilbert.boundedOperatorGraphMap (jointCommutatorCLM c)) b hb.le
      (jointCommutatorResolvent c b hb) (jointCommutatorResolvent_resolventEquation c b hb))
    (jointCommutatorKernelProjection_isStarProjection c)
    (commutantLaplacianCLM_commute_kernelProjection c)
    (jointCommutatorResolvent_commute_kernelProjection c b hb)
    (fun x ↦ by
      rw [← shiftedCommutantLaplacianCLM_apply, jointCommutatorResolvent_apply,
        ← shiftedCommutantLaplacianEquiv_apply]
      exact (shiftedCommutantLaplacianEquiv c b hb).symm_apply_apply x) B
  rw [re_inner_commutantLaplacianCLM] at h
  rw [jointCommutatorFirstPositiveGap, jointCommutatorResolventAllShifts_of_pos c b hb]
  exact h

/-- A positive value of `jointCommutatorFirstPositiveGap` is the attained least positive
eigenvalue of the commutant Laplacian. -/
theorem jointCommutatorFirstPositiveGap_isLeastPositiveEigenvalue {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ) (b : ℝ) (hb : 0 < b)
    (hpos : 0 < jointCommutatorFirstPositiveGap c b) :
    Module.End.HasEigenvalue (commutantLaplacianCLM c).toLinearMap
        ((jointCommutatorFirstPositiveGap c b : ℝ) : ℂ) ∧
      ∀ ν : ℝ, 0 < ν →
        Module.End.HasEigenvalue (commutantLaplacianCLM c).toLinearMap (ν : ℂ) →
          jointCommutatorFirstPositiveGap c b ≤ ν := by
  have hgap : jointCommutatorFirstPositiveGap c b =
      ‖SpectralGap.complementCompression (jointCommutatorResolvent c b hb)
        (jointCommutatorKernelProjection c)‖⁻¹ - b := by
    rw [jointCommutatorFirstPositiveGap, jointCommutatorResolventAllShifts_of_pos c b hb]
  have hne : SpectralGap.complementCompression (jointCommutatorResolvent c b hb)
      (jointCommutatorKernelProjection c) ≠ 0 := by
    intro h0
    rw [hgap, h0, norm_zero, inv_zero] at hpos
    linarith
  have h := jointCommutator_inverseNormGap_is_leastPositiveEigenvalue c b hb hne
  rw [hgap]
  exact ⟨h.2.1, h.2.2⟩

/-- The limiting complement gap `‖(1 − P_M) R (1 − P_M)‖⁻¹ − b` of a limit resolvent `R` at
shift `b` relative to a closed subspace `M`. -/
def graphLimitComplementGap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (R : H →L[ℂ] H) (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (b : ℝ) : ℝ :=
  ‖SpectralGap.complementCompression R M.starProjection‖⁻¹ - b

end RenewalGeometry

namespace RenewalGeometry.VaryingHilbert.System

universe u v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Hlim : Type w} [NormedAddCommGroup Hlim] [InnerProductSpace ℂ Hlim] [CompleteSpace Hlim]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- `J_∞ (J_∞^* J_∞ x) = J_∞ x`-type identity: the adjoint of the limit embedding is a left
inverse. -/
theorem limitAdjoint_apply_embedding (Jlim : Hlim →ₗᵢ[ℂ] H) (x : Hlim) :
    (Jlim.toContinuousLinearMap).adjoint (Jlim x) = x :=
  (constantEmbeddingSystem Jlim).adjointLift_embedding 0 x

theorem transportedLimitOperator_apply_embedding (Jlim : Hlim →ₗᵢ[ℂ] H) (T : Hlim →L[ℂ] Hlim)
    (x : Hlim) : transportedLimitOperator Jlim T (Jlim x) = Jlim (T x) := by
  rw [transportedLimitOperator_apply, limitAdjoint_apply_embedding]

omit [CompleteSpace H] in
/-- Joint continuity of operator application along norm-convergent operators. -/
theorem unboundedGapChain_tendsto_clm_apply (T : ℕ → H →L[ℂ] H) (Tl : H →L[ℂ] H) (y : ℕ → H) (yl : H)
    (hT : Tendsto T atTop (𝓝 Tl)) (hy : Tendsto y atTop (𝓝 yl)) :
    Tendsto (fun n ↦ T n (y n)) atTop (𝓝 (Tl yl)) :=
  ((isBoundedBilinearMap_apply (𝕜 := ℂ) (E := H) (F := H)).continuous.tendsto (Tl, yl)).comp
    (hT.prodMk_nhds hy)

/-- **Compact spectral gap chain for joint-commutator cutoffs with an unbounded limit on a
general limiting screened space.**  The cutoff commutator forms converge in the transported
Mosco sense (`def:transported-mosco`) to the closed form `‖A v‖²` of a densely defined
`A : D →ₗ F` on a limiting Hilbert space `H_∞` embedded isometrically by `J_∞` (weak resolvent
`R` at shift `b`), with compatibility `P_X → P_∞ = J_∞ J_∞^*` strongly and compact graph screens
(asymptotic form compactness).  With protected subspaces `M_X ⊆ Ker 𝓛_X` of the dimension of
the limiting kernel `M_∞ = Ker A` and a nonzero complement `M_∞ ≠ ⊤` in `H_∞`: `M_∞` is finite
dimensional; eventually `Ker 𝓛_X = M_X`; `R` is compact and
`‖J_X R_X J_X^* − J_∞ R J_∞^*‖ → 0`; the transported kernel projections converge in norm to
`J_∞ P_{M_∞} J_∞^*`; the limiting gap `γ_∞ = ‖(1 − P) R (1 − P)‖⁻¹ − b` is positive, attained on
an eigenvector in `D ∩ M_∞^⊥` and bounds the Rayleigh quotient on the complement (so
`γ_∞ = λ_{m+1}(𝓛_∞)`); `λ_{m+1}(𝓛_X) → γ_∞`; and the late-cutoff coercivity holds for every
`γ_0 < γ_∞`. -/
theorem jointCommutator_unboundedLimitGapChain
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
    (hMker : ∀ᶠ X in atTop,
      M X ≤ LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap)
    (Mlim : Submodule ℂ Hlim) [Mlim.HasOrthogonalProjection]
    (hMlim : operatorGraphKernel D A = Mlim)
    (hMrank : ∀ᶠ X in atTop, Module.finrank ℂ (M X) = Module.finrank ℂ Mlim)
    (hcompl : Mlim ≠ ⊤) :
    FiniteDimensional ℂ Mlim ∧
      (∀ᶠ X in atTop,
        LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap = M X) ∧
      IsCompactOperator R ∧
      Tendsto (J.compressedOperator (RenewalGeometry.jointCommutatorResolventFamily c b))
        atTop (𝓝 (transportedLimitOperator Jlim R)) ∧
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
            ‖v - Mlim.starProjection v‖ ^ 2 ≤ ‖A ⟨v, hv⟩‖ ^ 2) ∧
      (∀ γ0 : ℝ, γ0 < RenewalGeometry.graphLimitComplementGap R Mlim b →
        ∀ᶠ X in atTop, ∀ B : EuclideanSpace ℂ (d X × d X),
          γ0 * ‖B - (M X).starProjection B‖ ^ 2 ≤
            ‖RenewalGeometry.jointCommutatorCLM (c X) B‖ ^ 2) := by
  classical
  set Rn := RenewalGeometry.jointCommutatorResolventFamily c b with hRndef
  have hstageEq : ∀ X f, OperatorGraphResolventEquation
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (d X × d X)))
      (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c X))) b f (Rn X f) :=
    fun X f ↦ RenewalGeometry.jointCommutatorResolventFamily_resolventEquation c b hb X f
  -- collective compactness from the graph screens
  have hcc : J.CollectivelyCompact Rn :=
    J.operatorGraphResolvent_collectivelyCompact_of_graphScreenTails L
      (fun X ↦ (⊤ : Submodule ℂ (EuclideanSpace ℂ (d X × d X))))
      (fun X ↦ boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c X)))
      Rn b hb hstageEq screen hcompact htail hfst
  have hmosco' : J.TransportedMoscoConverges Jlim
      (fun X ↦ ennrealOperatorGraphEnergy (⊤ : Submodule ℂ (EuclideanSpace ℂ (d X × d X)))
        (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c X))))
      (ennrealOperatorGraphEnergy D A) := by
    simpa only [ennrealOperatorGraphEnergy_top] using hmosco
  -- norm-resolvent convergence
  set T : ℕ → H →L[ℂ] H := J.compressedOperator Rn with hTdef
  set Tlim : H →L[ℂ] H := transportedLimitOperator Jlim R with hTlimdef
  have hTconv : Tendsto T atTop (𝓝 Tlim) :=
    tendsto_compressedOperator_of_transportedMosco J Jlim
      (fun X ↦ (⊤ : Submodule ℂ (EuclideanSpace ℂ (d X × d X))))
      (fun X ↦ boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c X)))
      D A b hb Rn R hstageEq hlimitEquation hmosco' _ hcompat hcc
  have hstageCompact : ∀ X, IsCompactOperator (T X : H → H) := fun X ↦
    J.compressedOperator_isCompactOperator_of_finiteDimensional Rn X
  have hstageSymmetric : ∀ X, LinearMap.IsSymmetric (T X).toLinearMap := by
    intro X
    apply J.compressedOperator_isSymmetric
    intro n
    exact operatorGraphResolvent_isSymmetric _ _ b (Rn n) (hstageEq n)
  have hTlimCompact : IsCompactOperator (Tlim : H → H) :=
    isCompactOperator_of_tendsto hTconv (Eventually.of_forall hstageCompact)
  set Jc : Hlim →L[ℂ] H := Jlim.toContinuousLinearMap with hJc
  have hRsymm : LinearMap.IsSymmetric R.toLinearMap :=
    operatorGraphResolvent_isSymmetric D A b R hlimitEquation
  have hRpos : R.IsPositive :=
    operatorGraphResolvent_isPositive D A b hb.le R hlimitEquation
  have hTlimSymm : LinearMap.IsSymmetric Tlim.toLinearMap := by
    apply (constantEmbeddingSystem Jlim).compressedOperator_isSymmetric
    intro _; exact hRsymm
  have hTlimEq : Tlim = Jc ∘L R ∘L Jc.adjoint := rfl
  have hTlimPos : Tlim.IsPositive := by
    rw [hTlimEq]; exact hRpos.conj_adjoint Jc
  have hRcompact : IsCompactOperator (R : Hlim → Hlim) := by
    have h := (hTlimCompact.comp_clm Jc).clm_comp Jc.adjoint
    have hfun : (Jc.adjoint ∘ (Tlim ∘ Jc) : Hlim → Hlim) = R := by
      funext x
      simp only [Function.comp_apply]
      change Jc.adjoint (transportedLimitOperator Jlim R (Jlim x)) = R x
      rw [transportedLimitOperator_apply_embedding, limitAdjoint_apply_embedding]
    rw [hfun] at h
    exact h
  have hRnorm : ‖R‖ ≤ b⁻¹ := by
    simpa [one_div] using operatorGraphResolvent_opNorm_le_inv D A R b hb hlimitEquation
  have hTlimNorm : ‖Tlim‖ ≤ b⁻¹ := by
    have : ‖Tlim‖ = ‖R‖ := (constantEmbeddingSystem Jlim).norm_compressedOperator (fun _ ↦ R) 0
    rw [this]; exact hRnorm
  -- the Riesz circle around `1/b`
  set center : ℂ := (((1 / b : ℝ) : ℂ)) with hcenter
  have hcenter0 : center ≠ 0 := by
    rw [hcenter]; exact_mod_cast (one_div_pos.mpr hb).ne'
  obtain ⟨radius, hR, hzero, hlimitContour, hrangeEig⟩ :=
    RenewalGeometry.ResolventStability.exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isSymmetric
      Tlim hTlimCompact hTlimSymm center hcenter0
  set Q : ℕ → H →L[ℂ] H := fun X ↦
    RenewalGeometry.ResolventStability.circleRieszProjection (T X) center radius with hQdef
  set Qlim : H →L[ℂ] H :=
    RenewalGeometry.ResolventStability.circleRieszProjection Tlim center radius with hQlimdef
  set Pi : ℕ → H →L[ℂ] H :=
    J.compressedOperator (fun X ↦ RenewalGeometry.jointCommutatorKernelProjection (c X))
    with hPidef
  set Plim : Hlim →L[ℂ] Hlim := Mlim.starProjection with hPlimdef
  set Pilim : H →L[ℂ] H := transportedLimitOperator Jlim Plim with hPilimdef
  obtain ⟨Mb, hMb, hlimitBound⟩ :=
    RenewalGeometry.ResolventStability.exists_circle_resolvent_norm_bound
      Tlim center radius hlimitContour
  obtain ⟨Nb, hNb, hstageBound⟩ :=
    RenewalGeometry.ResolventStability.eventually_circle_resolvent_bound_of_tendsto
      T Tlim hTconv center radius Mb hMb hlimitContour hlimitBound
  have hcontour : ∀ᶠ X in atTop, ∀ z ∈ Metric.sphere center radius,
      z ∈ resolventSet ℂ (T X) :=
    hstageBound.mono fun _ hn z hz ↦ (hn z hz).1
  have hQconv : Tendsto Q atTop (𝓝 Qlim) :=
    RenewalGeometry.ResolventStability.circleRieszProjection_tendsto hTconv center radius hR.le
      Mb Nb hMb hlimitContour hlimitBound hcontour (hstageBound.mono fun _ hn z hz ↦ (hn z hz).2)
  have hfinite : ∀ᶠ X in atTop, Module.Finite ℂ (LinearMap.range (Q X).toLinearMap) := by
    filter_upwards [hcontour] with X hX
    exact RenewalGeometry.ResolventStability.finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
      (T X) (hstageCompact X) (hstageSymmetric X) center radius hR hzero hX
  have hidemQ : ∀ᶠ X in atTop, IsIdempotentElem (Q X) := by
    filter_upwards [hcontour] with X hX
    exact ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp
      (RenewalGeometry.ResolventStability.circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
        (T X) (hstageCompact X) (hstageSymmetric X) center radius hR hX)
  have hinsideB : (((b : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius := by
    simpa [hcenter, one_div] using (Metric.mem_ball_self hR : center ∈ Metric.ball center radius)
  have hkernelRiesz : ∀ᶠ X in atTop,
      (LinearMap.ker (RenewalGeometry.jointCommutatorCLM (c X)).toLinearMap).map
          (J.embedding X).toLinearMap ≤ LinearMap.range (Q X).toLinearMap := by
    filter_upwards [hcontour] with X hX
    rw [← J.eigenspace_compressed_jointCommutatorResolventFamily c b hb X]
    exact RenewalGeometry.ResolventStability.eigenspace_le_range_circleRieszProjection_of_mem_ball
      (T X) center (((b : ℝ) : ℂ)⁻¹) radius hinsideB hX
  -- the limiting Riesz range is the transported limiting kernel
  have hbinv : center = (((b : ℝ) : ℂ)⁻¹) := by
    rw [hcenter]; push_cast; rw [one_div]
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have heigMap : Module.End.eigenspace Tlim.toLinearMap center = Mlim.map Jlim.toLinearMap := by
    ext x
    rw [Module.End.mem_eigenspace_iff, hbinv]
    constructor
    · intro hx
      change Tlim x = _ at hx
      set u : Hlim := ((b : ℝ) : ℂ) • R (Jc.adjoint x) with hu
      have hxu : x = Jlim u := by
        rw [hu, map_smul]
        change x = ((b : ℝ) : ℂ) • Tlim x
        rw [hx, smul_smul, mul_inv_cancel₀ hbC, one_smul]
      have hRu : R u = (((b : ℝ) : ℂ)⁻¹) • u := by
        apply Jlim.injective
        rw [← transportedLimitOperator_apply_embedding, ← hxu, map_smul, ← hxu]
        exact hx
      refine ⟨u, ?_, hxu.symm⟩
      have hker : u ∈ operatorGraphKernel D A :=
        (mem_operatorGraphKernel_iff_resolvent_eigenvector D A b hb R hlimitEquation u).mpr hRu
      rw [hMlim] at hker
      exact hker
    · rintro ⟨u, hu0, rfl⟩
      have hu1 : u ∈ operatorGraphKernel D A := by rw [hMlim]; exact hu0
      have hu := (mem_operatorGraphKernel_iff_resolvent_eigenvector D A b hb R hlimitEquation u).mp
        hu1
      change Tlim (Jlim u) = _
      rw [transportedLimitOperator_apply_embedding, hu, map_smul]
      rfl
  have hQlimRange : LinearMap.range Qlim.toLinearMap = Mlim.map Jlim.toLinearMap :=
    hrangeEig.trans heigMap
  have hstarQlim : IsStarProjection Qlim :=
    RenewalGeometry.ResolventStability.circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
      Tlim hTlimCompact hTlimSymm center radius hR hlimitContour
  have hstarPilim : IsStarProjection Pilim :=
    (constantEmbeddingSystem Jlim).compressedOperator_isStarProjection (fun _ ↦ Plim) 0
      isStarProjection_starProjection
  have hPilimRange : LinearMap.range Pilim.toLinearMap = Mlim.map Jlim.toLinearMap :=
    (constantEmbeddingSystem Jlim).compressedOperator_starProjection_range (fun _ ↦ Mlim) 0
  have hQlimEq : Qlim = Pilim := by
    apply ContinuousLinearMap.IsStarProjection.ext hstarQlim hstarPilim
    change LinearMap.range Qlim.toLinearMap = LinearMap.range Pilim.toLinearMap
    rw [hQlimRange, hPilimRange]
  have hQlimCompact : IsCompactOperator (Qlim : H → H) :=
    RenewalGeometry.ResolventStability.circleRieszProjection_isCompactOperator
      Tlim hTlimCompact center radius hR hzero hlimitContour
  letI hQlimFin : Module.Finite ℂ (LinearMap.range Qlim.toLinearMap) :=
    RenewalGeometry.ResolventStability.finiteDimensional_range_of_compact_idempotent
      Qlim hQlimCompact hstarQlim.isIdempotentElem
  have hmapFin : FiniteDimensional ℂ (Mlim.map Jlim.toLinearMap) := by
    rw [← hQlimRange]; exact hQlimFin
  have hmapRank : Module.finrank ℂ (Mlim.map Jlim.toLinearMap) = Module.finrank ℂ Mlim :=
    (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective Jlim.toLinearMap Jlim.injective Mlim)).symm
  have hMlimFin : FiniteDimensional ℂ Mlim :=
    LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective Jlim.toLinearMap Jlim.injective Mlim).symm
  have hQrank : ∀ᶠ X in atTop,
      Module.finrank ℂ (LinearMap.range (Q X).toLinearMap) =
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap) :=
    RenewalGeometry.ProjectionStability.eventually_finrank_range_eq_of_tendsto Q Qlim hQconv
      (hidemQ.mono fun _ hn ↦ ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr hn)
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr hstarQlim.isIdempotentElem)
      hfinite
  -- kernel locking
  have hlock : ∀ᶠ X in atTop,
      LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap = M X ∧
        (LinearMap.ker (RenewalGeometry.jointCommutatorCLM (c X)).toLinearMap).map
          (J.embedding X).toLinearMap = LinearMap.range (Q X).toLinearMap := by
    filter_upwards [hMker, hMrank, hQrank, hfinite, hkernelRiesz] with X hMX hrX hQX hfinX hkerX
    letI : Module.Finite ℂ (LinearMap.range (Q X).toLinearMap) := hfinX
    rw [RenewalGeometry.ker_commutantLaplacianCLM] at hMX ⊢
    set K := LinearMap.ker (RenewalGeometry.jointCommutatorCLM (c X)).toLinearMap with hK
    have h1 : Module.finrank ℂ (K.map (J.embedding X).toLinearMap) = Module.finrank ℂ K :=
      (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective _ (J.embedding X).injective K)).symm
    have h2 : Module.finrank ℂ (K.map (J.embedding X).toLinearMap) ≤
        Module.finrank ℂ (LinearMap.range (Q X).toLinearMap) := Submodule.finrank_mono hkerX
    have h3 : Module.finrank ℂ (LinearMap.range (Q X).toLinearMap) =
        Module.finrank ℂ (M X) := by
      rw [hQX, hQlimRange, hmapRank, hrX]
    have h4 : Module.finrank ℂ (M X) ≤ Module.finrank ℂ K := Submodule.finrank_mono hMX
    refine ⟨(Submodule.eq_of_le_of_finrank_eq hMX (by omega)).symm, ?_⟩
    exact Submodule.eq_of_le_of_finrank_eq hkerX (by omega)
  -- projection convergence
  have hstarPi : ∀ X, IsStarProjection (Pi X) := fun X ↦
    J.compressedOperator_isStarProjection _ X
      (RenewalGeometry.jointCommutatorKernelProjection_isStarProjection (c X))
  have hPiQ : ∀ᶠ X in atTop,
      LinearMap.range (Pi X).toLinearMap = LinearMap.range (Q X).toLinearMap := by
    filter_upwards [hlock] with X hX
    rw [hPidef, J.range_compressedOperator,
      RenewalGeometry.range_jointCommutatorKernelProjection]
    exact hX.2
  have hPiconv : Tendsto Pi atTop (𝓝 Qlim) :=
    RenewalGeometry.ProjectionStability.starProjection_tendsto_of_idempotent_range_eq
      Pi Q Qlim (Eventually.of_forall hstarPi) hidemQ hstarQlim hPiQ hQconv
  -- commutation and nonvanishing on the limiting space
  have hcommuteT : Commute Tlim Qlim :=
    RenewalGeometry.ResolventStability.circleRieszProjection_commute_of_compact_of_isSymmetric
      Tlim hTlimCompact hTlimSymm center radius hR hlimitContour
  have hcommute : Commute R Plim := by
    apply ContinuousLinearMap.ext
    intro x
    change R (Plim x) = Plim (R x)
    apply Jlim.injective
    have h := congrArg (fun S : H →L[ℂ] H ↦ S (Jlim x)) hcommuteT.eq
    change Tlim (Qlim (Jlim x)) = Qlim (Tlim (Jlim x)) at h
    rw [hQlimEq] at h
    change Tlim (Pilim (Jlim x)) = Pilim (Tlim (Jlim x)) at h
    rw [hPilimdef, transportedLimitOperator_apply_embedding, hTlimdef,
      transportedLimitOperator_apply_embedding, transportedLimitOperator_apply_embedding,
      transportedLimitOperator_apply_embedding] at h
    exact h
  have hPne : Plim ≠ 1 := by
    intro h1
    apply hcompl
    rw [eq_top_iff]
    intro x _
    have : Plim x = x := by rw [h1]; rfl
    rw [← this]
    exact Submodule.starProjection_apply_mem Mlim x
  have hneLim : RenewalGeometry.SpectralGap.complementCompression R Plim ≠ 0 :=
    RenewalGeometry.SpectralGap.complementCompression_ne_zero_of_injective_of_commute
      R Plim (operatorGraphResolvent_injective D A b R hDdense hlimitEquation)
      isStarProjection_starProjection hcommute hPne
  have hnormEq : ‖RenewalGeometry.SpectralGap.complementCompression Tlim Qlim‖ =
      ‖RenewalGeometry.SpectralGap.complementCompression R Plim‖ := by
    rw [hQlimEq]
    exact (constantEmbeddingSystem Jlim).norm_complementCompression_compressedOperator
      (fun _ ↦ R) (fun _ ↦ Plim) 0
  have hne : RenewalGeometry.SpectralGap.complementCompression Tlim Qlim ≠ 0 := by
    intro h0
    apply hneLim
    rw [← norm_eq_zero, ← hnormEq, h0, norm_zero]
  have hgapEqLim : RenewalGeometry.graphLimitComplementGap R Mlim b =
      ‖RenewalGeometry.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - b := by
    rw [RenewalGeometry.graphLimitComplementGap, hnormEq]
  have hgapPos : 0 < ‖RenewalGeometry.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - b :=
    RenewalGeometry.SpectralGap.inverseNormGap_circleRieszProjection_pos
      Tlim hTlimCompact hTlimPos center radius hR hlimitContour b hb hinsideB
        hTlimNorm hne
  -- gap convergence
  have hgapTendsto0 : Tendsto
      (fun X ↦ ‖RenewalGeometry.SpectralGap.complementCompression (T X) (Pi X)‖⁻¹ - b)
      atTop (𝓝 (‖RenewalGeometry.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - b)) :=
    RenewalGeometry.SpectralGap.inverseNormGap_tendsto_of_idempotent_ranges
      T Pi Q Tlim Qlim b hTconv hQconv (Eventually.of_forall hstarPi) hidemQ hstarQlim hPiQ
      (norm_ne_zero_iff.mpr hne)
  have hstageGapEq : ∀ X,
      ‖RenewalGeometry.SpectralGap.complementCompression (T X) (Pi X)‖⁻¹ - b =
        RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b := by
    intro X
    rw [hTdef, hPidef, J.norm_complementCompression_compressedOperator]
    rfl
  have hgapTendsto : Tendsto (fun X ↦ RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b)
      atTop (𝓝 (RenewalGeometry.graphLimitComplementGap R Mlim b)) := by
    rw [hgapEqLim]
    simpa only [hstageGapEq] using hgapTendsto0
  have hgapPos' : 0 < RenewalGeometry.graphLimitComplementGap R Mlim b := by
    rw [hgapEqLim]; exact hgapPos
  have hstagePos : ∀ᶠ X in atTop, 0 < RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b :=
    hgapTendsto.eventually (Ioi_mem_nhds hgapPos')
  have hstageEigen : ∀ᶠ X in atTop,
      0 < RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b ∧
        Module.End.HasEigenvalue
          (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap
          ((RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b : ℝ) : ℂ) ∧
        ∀ ν : ℝ, 0 < ν →
          Module.End.HasEigenvalue
            (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap (ν : ℂ) →
            RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b ≤ ν := by
    filter_upwards [hstagePos] with X hX
    exact ⟨hX, RenewalGeometry.jointCommutatorFirstPositiveGap_isLeastPositiveEigenvalue
      (c X) b hb hX⟩
  -- late-cutoff coercivity
  have hcoerciveKer : ∀ γ0 : ℝ, γ0 < RenewalGeometry.graphLimitComplementGap R Mlim b →
      ∀ᶠ X in atTop, ∀ B : EuclideanSpace ℂ (d X × d X),
        γ0 * ‖B - RenewalGeometry.jointCommutatorKernelProjection (c X) B‖ ^ 2 ≤
          ‖RenewalGeometry.jointCommutatorCLM (c X) B‖ ^ 2 := by
    intro γ0 hγ0
    filter_upwards [hgapTendsto.eventually (Ioi_mem_nhds hγ0)] with X hX
    intro B
    have h := RenewalGeometry.jointCommutatorFirstPositiveGap_coercivity (c X) b hb B
    have hX' : γ0 ≤ RenewalGeometry.jointCommutatorFirstPositiveGap (c X) b := le_of_lt hX
    nlinarith [sq_nonneg ‖B - RenewalGeometry.jointCommutatorKernelProjection (c X) B‖]
  have hcoercive : ∀ γ0 : ℝ, γ0 < RenewalGeometry.graphLimitComplementGap R Mlim b →
      ∀ᶠ X in atTop, ∀ B : EuclideanSpace ℂ (d X × d X),
        γ0 * ‖B - (M X).starProjection B‖ ^ 2 ≤
          ‖RenewalGeometry.jointCommutatorCLM (c X) B‖ ^ 2 := by
    intro γ0 hγ0
    filter_upwards [hcoerciveKer γ0 hγ0, hlock] with X hX hlockX
    intro B
    have hproj : (M X).starProjection =
        RenewalGeometry.jointCommutatorKernelProjection (c X) := by
      apply ContinuousLinearMap.IsStarProjection.ext isStarProjection_starProjection
        (RenewalGeometry.jointCommutatorKernelProjection_isStarProjection (c X))
      rw [Submodule.range_starProjection]
      change M X = LinearMap.range
        (RenewalGeometry.jointCommutatorKernelProjection (c X)).toLinearMap
      rw [RenewalGeometry.range_jointCommutatorKernelProjection, ← hlockX.1,
        RenewalGeometry.ker_commutantLaplacianCLM]
    rw [hproj]
    exact hX B
  -- limit variational bound along recovery sequences
  have hvariational : ∀ v : Hlim, ∀ hv : v ∈ D,
      RenewalGeometry.graphLimitComplementGap R Mlim b *
          ‖v - Mlim.starProjection v‖ ^ 2 ≤ ‖A ⟨v, hv⟩‖ ^ 2 := by
    intro v hv
    have hqfin : ennrealOperatorGraphEnergy D A v ≠ ∞ :=
      (ennrealOperatorGraphEnergy_ne_top_iff D A v).mpr hv
    obtain ⟨x, hx, hqx⟩ := hmosco.recovery v hqfin
    have hJx : Tendsto (fun X ↦ J.embedding X (x X)) atTop (𝓝 (Jlim v)) := hx
    have hPiapply : Tendsto (fun X ↦ Pi X (J.embedding X (x X))) atTop
        (𝓝 (Qlim (Jlim v))) :=
      unboundedGapChain_tendsto_clm_apply Pi Qlim _ _ hPiconv hJx
    have hresid : Tendsto (fun X ↦ ‖J.embedding X (x X) - Pi X (J.embedding X (x X))‖)
        atTop (𝓝 ‖v - Mlim.starProjection v‖) := by
      have hlimval : ‖Jlim v - Qlim (Jlim v)‖ = ‖v - Mlim.starProjection v‖ := by
        rw [hQlimEq, hPilimdef, transportedLimitOperator_apply_embedding, ← map_sub,
          LinearIsometry.norm_map]
      rw [← hlimval]
      exact (hJx.sub hPiapply).norm
    have hresidEq : ∀ X, ‖J.embedding X (x X) - Pi X (J.embedding X (x X))‖ =
        ‖x X - RenewalGeometry.jointCommutatorKernelProjection (c X) (x X)‖ := by
      intro X
      have hPiJ : Pi X (J.embedding X (x X)) =
          J.embedding X (RenewalGeometry.jointCommutatorKernelProjection (c X) (x X)) := by
        simp [hPidef, compressedOperator, J.adjointLift_embedding]
      rw [hPiJ, ← map_sub, LinearIsometry.norm_map]
    have hqreal : Tendsto (fun X ↦ ‖RenewalGeometry.jointCommutatorCLM (c X) (x X)‖ ^ 2) atTop
        (𝓝 (‖A ⟨v, hv⟩‖ ^ 2)) := by
      have h := (ENNReal.tendsto_toReal hqfin).comp hqx
      rw [ennrealOperatorGraphEnergy_toReal D A v hv] at h
      refine h.congr' (Eventually.of_forall fun X ↦ ?_)
      simp only [Function.comp_apply]
      rw [ennrealBoundedOperatorEnergy, ENNReal.toReal_ofReal (sq_nonneg _)]
    have hγ0 : ∀ γ0 : ℝ, γ0 < RenewalGeometry.graphLimitComplementGap R Mlim b →
        γ0 * ‖v - Mlim.starProjection v‖ ^ 2 ≤ ‖A ⟨v, hv⟩‖ ^ 2 := by
      intro γ0 hlt
      refine le_of_tendsto_of_tendsto ((hresid.pow 2).const_mul γ0) hqreal ?_
      filter_upwards [hcoerciveKer γ0 hlt] with X hX
      rw [hresidEq X]
      exact hX (x X)
    by_cases hr : ‖v - Mlim.starProjection v‖ ^ 2 = 0
    · rw [hr, mul_zero]; exact sq_nonneg _
    have hrpos : 0 < ‖v - Mlim.starProjection v‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hr)
    have hle : RenewalGeometry.graphLimitComplementGap R Mlim b ≤
        ‖A ⟨v, hv⟩‖ ^ 2 / ‖v - Mlim.starProjection v‖ ^ 2 := by
      apply le_of_forall_lt_imp_le_of_dense
      intro γ0 hlt
      rw [le_div_iff₀ hrpos]
      exact hγ0 γ0 hlt
    rwa [le_div_iff₀ hrpos] at hle
  -- the attained limiting eigenvector, on the limiting space
  obtain ⟨w, hw0, hPw, hRw⟩ :=
    RenewalGeometry.SpectralGap.exists_eigenvector_norm_complementCompression
      R Plim hRcompact hRpos isStarProjection_starProjection hcommute hneLim
  set t := ‖RenewalGeometry.SpectralGap.complementCompression R Plim‖ with htdef
  have htpos : 0 < t := norm_pos_iff.mpr hneLim
  have hγt : RenewalGeometry.graphLimitComplementGap R Mlim b + b = t⁻¹ := by
    rw [RenewalGeometry.graphLimitComplementGap]; ring
  have hwD : w ∈ D := by
    have hw : w = (((t⁻¹ : ℝ)) : ℂ) • R w := by
      rw [hRw, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ htpos.ne',
        Complex.ofReal_one, one_smul]
    rw [hw]
    exact D.smul_mem _ (hlimitEquation w).mem
  have heig : ∃ v : Hlim, ∃ hv : v ∈ D, v ≠ 0 ∧ v ∈ Mlimᗮ ∧
      R v = (((RenewalGeometry.graphLimitComplementGap R Mlim b + b)⁻¹ : ℝ) : ℂ) • v ∧
      ‖A ⟨v, hv⟩‖ ^ 2 = RenewalGeometry.graphLimitComplementGap R Mlim b * ‖v‖ ^ 2 := by
    refine ⟨w, hwD, hw0, ?_, ?_, ?_⟩
    · rw [← Submodule.starProjection_apply_eq_zero_iff]
      exact hPw
    · rw [hγt, inv_inv]
      exact hRw
    · have E := hlimitEquation w
      have heul := E.weakEuler ⟨w, hwD⟩
      have hsub : (⟨R w, E.mem⟩ : D) = ((t : ℝ) : ℂ) • (⟨w, hwD⟩ : D) := by
        apply Subtype.ext
        simp only [SetLike.val_smul]
        exact hRw
      rw [hsub, map_smul] at heul
      change (inner ℂ (((t : ℝ) : ℂ) • A ⟨w, hwD⟩) (A ⟨w, hwD⟩)).re +
          b * (inner ℂ (R w) w).re = (inner ℂ w w).re at heul
      rw [hRw, inner_smul_left, inner_smul_left,
        Complex.conj_ofReal, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at heul
      have hA2 : (inner ℂ (A ⟨w, hwD⟩) (A ⟨w, hwD⟩)).re = ‖A ⟨w, hwD⟩‖ ^ 2 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
      have hw2 : (inner ℂ w w).re = ‖w‖ ^ 2 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
      rw [hA2, hw2] at heul
      have hγ : RenewalGeometry.graphLimitComplementGap R Mlim b = t⁻¹ - b := by
        linarith [hγt]
      rw [hγ]
      have h' : t * ‖A ⟨w, hwD⟩‖ ^ 2 = ‖w‖ ^ 2 - b * (t * ‖w‖ ^ 2) := by linarith
      calc ‖A ⟨w, hwD⟩‖ ^ 2 = t⁻¹ * (t * ‖A ⟨w, hwD⟩‖ ^ 2) := by
            rw [← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul]
        _ = t⁻¹ * (‖w‖ ^ 2 - b * (t * ‖w‖ ^ 2)) := by rw [h']
        _ = (t⁻¹ - b) * ‖w‖ ^ 2 := by
            rw [mul_sub, ← mul_assoc, ← mul_assoc, mul_comm t⁻¹ b, mul_assoc b,
              inv_mul_cancel₀ htpos.ne', mul_one]
            ring
  have hPiconv' : Tendsto Pi atTop (𝓝 Pilim) := by
    rw [← hQlimEq]; exact hPiconv
  exact ⟨hMlimFin, hlock.mono fun X hX ↦ hX.1, hRcompact, hTconv,
    hPiconv', hgapPos', hgapTendsto, hstageEigen, heig, hvariational, hcoercive⟩

end RenewalGeometry.VaryingHilbert.System
