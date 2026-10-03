/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.CofinalSpectralUpgradeUnboundedExact
import RenewalGeometry.OperatorLimits.CofinalAsymptoticCompactness

/-!
# Compact spectral upgrade under asymptotic form compactness

Covers `cor:cofinal-spectral-upgrade` of the spacetime–gauge duality manuscript with the
paper's own compactness hypothesis, `def:asymptotic-compactness`, in place of the compact
graph-screen tail used by `cofinalSpectralUpgradeUnbounded_exact`.

The asymptotic-compactness hypothesis is `CofinallyAsymptoticallyCompactFamily`
(`OperatorLimits/CofinalAsymptoticCompactness.lean`): the named predicate
`System.AsymptoticallyCompact` on every cofinal subfamily of cutoffs, plus `LimitFormCompact`.
It involves only the transported cutoff vectors `J_X A_X` and the energies `q_X(A_X)`; no
compactness of the commutator components is assumed.

* `jointCommutator_collectivelyCompact_of_cofinallyAsymptoticallyCompact`: the finite cutoff
  commutator resolvents are collectively compact (`lem:collective-compactness`).
* `jointCommutator_unboundedLimitGapChain_of_collectivelyCompact`: the compact spectral gap chain
  of `JointCommutatorUnboundedLimitGapChain.lean`, run from collective compactness alone.
* `cofinalSpectralUpgrade_asymptoticallyCompact_exact` (`cor:cofinal-spectral-upgrade`).
* `cofinalSpectralUpgrade_asymptoticallyCompact_nonvacuous`: the hypothesis packet is
  satisfiable (constant cutoffs `diag(1,0)` on `2 × 2` matrices, proper commutant).
-/

open Complex Filter Set Topology Matrix
open scoped ENNReal

noncomputable section

namespace RenewalGeometry.VaryingHilbert.System

universe u v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Hlim : Type w} [NormedAddCommGroup Hlim] [InnerProductSpace ℂ Hlim] [CompleteSpace Hlim]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **`lem:collective-compactness` for the commutator cutoffs.**  If the cutoff commutator
forms `q_X(B) = ‖∂_X B‖²` are asymptotically compact along every cofinal subfamily of cutoffs,
the shift-`b` cutoff resolvents `(𝓛_X + b)⁻¹` are collectively compact. -/
theorem jointCommutator_collectivelyCompact_of_cofinallyAsymptoticallyCompact
    {d : ℕ → Type u} [∀ X, Fintype (d X)] {s : ℕ}
    (c : ∀ X, Fin s → Matrix (d X) (d X) ℂ)
    (J : System (K := ℂ) (H := H) (Hn := fun X ↦ EuclideanSpace ℂ (d X × d X)))
    (b : ℝ) (hb : 0 < b)
    (hac : J.CofinallyAsymptoticallyCompact
      (fun X ↦ ennrealBoundedOperatorEnergy (RenewalGeometry.jointCommutatorCLM (c X)))) :
    J.CollectivelyCompact (RenewalGeometry.jointCommutatorResolventFamily c b) := by
  apply collectivelyCompact_of_cofinallyAsymptoticallyCompact J
    (fun X ↦ (⊤ : Submodule ℂ (EuclideanSpace ℂ (d X × d X))))
    (fun X ↦ boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c X))) b hb _
    (fun X f ↦ RenewalGeometry.jointCommutatorResolventFamily_resolventEquation c b hb X f)
  simpa only [ennrealOperatorGraphEnergy_top] using hac

/-- **Compact spectral gap chain for joint-commutator cutoffs with an unbounded limit on a
general limiting screened space.**  The cutoff commutator forms converge in the transported
Mosco sense (`def:transported-mosco`) to the closed form `‖A v‖²` of a densely defined
`A : D →ₗ F` on a limiting Hilbert space `H_∞` embedded isometrically by `J_∞` (weak resolvent
`R` at shift `b`), with compatibility `P_X → P_∞ = J_∞ J_∞^*` strongly and **collectively compact** cutoff
resolvents (in place of the compact graph screens of
`jointCommutator_unboundedLimitGapChain`; the proof is otherwise identical).  With protected subspaces `M_X ⊆ Ker 𝓛_X` of the dimension of
the limiting kernel `M_∞ = Ker A` and a nonzero complement `M_∞ ≠ ⊤` in `H_∞`: `M_∞` is finite
dimensional; eventually `Ker 𝓛_X = M_X`; `R` is compact and
`‖J_X R_X J_X^* − J_∞ R J_∞^*‖ → 0`; the transported kernel projections converge in norm to
`J_∞ P_{M_∞} J_∞^*`; the limiting gap `γ_∞ = ‖(1 − P) R (1 − P)‖⁻¹ − b` is positive, attained on
an eigenvector in `D ∩ M_∞^⊥` and bounds the Rayleigh quotient on the complement (so
`γ_∞ = λ_{m+1}(𝓛_∞)`); `λ_{m+1}(𝓛_X) → γ_∞`; and the late-cutoff coercivity holds for every
`γ_0 < γ_∞`. -/
theorem jointCommutator_unboundedLimitGapChain_of_collectivelyCompact
    {d : ℕ → Type u} [∀ X, Fintype (d X)] {s : ℕ}
    (c : ∀ X, Fin s → Matrix (d X) (d X) ℂ)
    (J : System (K := ℂ) (H := H) (Hn := fun X ↦ EuclideanSpace ℂ (d X × d X)))
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
    (hcc : J.CollectivelyCompact (RenewalGeometry.jointCommutatorResolventFamily c b))
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

/-- **Compact spectral upgrade (`cor:cofinal-spectral-upgrade`) under asymptotic form
compactness.**  Assume the hypotheses of `thm:cofinal-duality` exactly as in
`derivedKernelCofinalDuality_exact`: (D1) transported Mosco convergence (`def:transported-mosco`)
of the cutoff commutator forms `q_X(B) = Σ_j ‖[c_{j,X}, B]‖²_HS` to the limiting form on `H_∞`
embedded isometrically by `J_∞` — the closed form `q_∞(v) = ‖A v‖²` of a densely defined
`A : D →ₗ F` with weak resolvent `R` at shift `b > 0` — with `P_X → P_∞ = J_∞ J_∞^*` strongly;
(D2) protected subspaces `M_X ⊆ Ker 𝓛_X` with orthonormal bases indexed by one finite type and
a specified `M_∞` with basis transport `η_X → 0`; (D3) a uniform late-cutoff gap `γ_* > 0`.
Assume in addition asymptotic form compactness (`def:asymptotic-compactness`, for the cofinal
family of cutoffs: `CofinallyAsymptoticallyCompactFamily`) and a nonzero complement
`M_∞ ≠ H_∞`.  Then, besides the parent conclusions (`Ker 𝓛_X = M_X = C^*(c_X)'` late,
`Ker 𝓛_∞ = M_∞`, `dim M_∞ = m`):

* `eq:limit-gap`: `γ_∞ := λ_{m+1}(𝓛_∞) ≥ γ_* > 0`, `γ_∞` attained on an eigenvector in
  `D ∩ M_∞^⊥` and minimising the Rayleigh quotient on the complement;
* `eq:cofinal-norm-resolvent`: `‖J_X R_X J_X^* − J_∞ R J_∞^*‖ → 0`, `R` compact;
* `eq:cofinal-spectral-upgrade`: `λ_{m+1}(𝓛_X) → γ_∞` (`λ_{m+1}(𝓛_X)` the attained least
  positive eigenvalue at late cutoffs) and `‖Π_X − Π_∞‖ → 0`, `Π_∞ = J_∞ P_{M_∞} J_∞^*`;
* `eq:cofinal-coercivity`: for every `0 < γ_0 < γ_∞` and all late cutoffs
  `q_X(B) ≥ γ_0 ‖(I − P_{M_X})B‖²`. -/
theorem cofinalSpectralUpgrade_asymptoticallyCompact_exact
    {d : ℕ → Type u} [∀ X, Fintype (d X)] [∀ X, DecidableEq (d X)] {s : ℕ}
    (c : ∀ X, Fin s → Matrix (d X) (d X) ℂ)
    (hstar : ∀ X j, ∃ k, (c X j)ᴴ = c X k)
    (J : System (K := ℂ) (H := H) (Hn := fun X ↦ EuclideanSpace ℂ (d X × d X)))
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
    (hAC : CofinallyAsymptoticallyCompactFamily J Jlim
      (fun X ↦ ennrealBoundedOperatorEnergy (RenewalGeometry.jointCommutatorCLM (c X)))
      (ennrealOperatorGraphEnergy D A))
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
  -- asymptotic form compactness gives collective compactness of the cutoff resolvents
  have hcc := jointCommutator_collectivelyCompact_of_cofinallyAsymptoticallyCompact c J b hb hAC.1
  obtain ⟨hfin, -, hcompactR, hTconv, hproj, hpos, hgap, heig, hvec, hvar, hcoer⟩ :=
    J.jointCommutator_unboundedLimitGapChain_of_collectivelyCompact c Jlim hcompat D A R hD1
      hDdense b hb hlimitEquation hcc M (Eventually.of_forall hMker) Mlim hMlim
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

/-! ### Non-vacuity witness -/

namespace RenewalGeometry.VaryingHilbert.System.UnboundedSpectralUpgradeWitness

/-- **Non-vacuity of `cofinalSpectralUpgrade_asymptoticallyCompact_exact`.**  All hypotheses
(including (D1)–(D3) of `thm:cofinal-duality`, asymptotic form compactness of the cofinal
family and the nonzero complement) hold for the constant cutoffs `c_X = diag(1, 0)` on `2 × 2`
matrices, whose commutant is a proper subspace; the theorem then yields a positive limit gap and
norm-resolvent convergence. -/
theorem cofinalSpectralUpgrade_asymptoticallyCompact_nonvacuous :
    0 < RenewalGeometry.graphLimitComplementGap Rw Kw 1 ∧
      Tendsto (Jw.compressedOperator
          (RenewalGeometry.jointCommutatorResolventFamily (fun _ : ℕ ↦ gen) 1))
        atTop (𝓝 (transportedLimitOperator LinearIsometry.id Rw)) := by
  obtain ⟨-, -, -, -, hγ, hγle, -, -, -, hT, -⟩ :=
    cofinalSpectralUpgrade_asymptoticallyCompact_exact (fun _ ↦ gen) hstar Jw LinearIsometry.id
      hcompatW ⊤ (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM gen)) Rw hmoscoT
      hDdense 1 one_pos hlimitEquation (fun _ ↦ Kw) (fun _ ↦ ew) (fun _ ↦ ew_orthonormal)
      (fun _ ↦ ew_span) (fun _ ↦ Kw_le_ker) Kw ew ew_orthonormal ew_span hη _ gap_pos hD3
      (cofinallyAsymptoticallyCompactFamily_of_properSpace Jw LinearIsometry.id _ _) Kw_ne_top
  exact ⟨hγ.trans_le hγle, hT⟩

end RenewalGeometry.VaryingHilbert.System.UnboundedSpectralUpgradeWitness
