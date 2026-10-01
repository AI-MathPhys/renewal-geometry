/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.TransportedMoscoStrongResolventConvergence
import RenewalGeometry.OperatorLimits.LowSpectrumConvergence
import RenewalGeometry.OperatorLimits.OperatorGraphResolventGraphScreen
import RenewalGeometry.OperatorLimits.OperatorGraphResolventPositivity
import RenewalGeometry.OperatorLimits.ContourResolventBounds
import RenewalGeometry.OperatorLimits.CompactCircleRieszProjection
import RenewalGeometry.OperatorLimits.BoundedOperatorNormalResolventFamily

/-!
# Compact Mosco convergence with a general limiting screened space

Covers `prop:compact-mosco-resolvent` of the spacetime–gauge duality manuscript in the paper's
generality: the cutoff forms converge in the transported Mosco sense of `def:transported-mosco`
(`System.TransportedMoscoConverges`) to a limiting form on an arbitrary limiting Hilbert space
`H_∞`, embedded isometrically into the common carrier by `J_∞` (possibly a proper subspace),
under the compatibility `P_X → P_∞ = J_∞ J_∞^*` strongly; asymptotic form compactness is
rendered by a compact graph-screen tail for the cutoff graph resolvents.

* `courantValue_isometryConj`: the Courant–Fischer values (ordered eigenvalues) of a positive
  operator are unchanged by isometric transport `T ↦ e T e^*`.  Hence the ordered eigenvalues of
  the transported resolvents are the intrinsic ones on `H_X` and on `H_∞`.
* `compactMoscoResolvent_general_exact`: norm-resolvent convergence
  `‖J_X R_X J_X^* − J_∞ R_∞ J_∞^*‖ → 0` (`eq:norm-resolvent`), compactness and positivity of
  `R_∞`, ordered-eigenvalue convergence `μ_{k,X} → μ_{k,∞}` and
  `λ_{k,X} = μ_{k,X}⁻¹ − b → λ_{k,∞}` whenever `μ_{k,∞} > 0` (`eq:eigenvalue-convergence`, with
  `μ_{k,·}` the intrinsic ordered eigenvalues of `R_X` on `H_X` and of `R_∞` on `H_∞`), and the
  isolated-cluster clause: for every circle in the resolvent set avoiding `0`, the transported
  Riesz projections converge in norm and their (finite) ranks are eventually equal.
* `CompactMoscoGeneralWitness.compactMoscoResolvent_general_nonvacuous`: the hypothesis packet is
  satisfied with a **proper** limiting subspace (`H_∞ = ℂ` embedded as the line `ℂ e₀ ⊂ ℂ²`).
-/

open Filter Topology Complex
open scoped ENNReal InnerProductSpace
open RenewalGeometry.CourantFischer RenewalGeometry.LowSpectrum

noncomputable section

namespace RenewalGeometry.VaryingHilbert.System

universe u v w w' z z'

section IsometryConj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The adjoint of an isometry is a left inverse. -/
theorem isometry_adjoint_apply_self (e : E →ₗᵢ[ℂ] G) (x : E) :
    (e.toContinuousLinearMap).adjoint (e x) = x :=
  (constantEmbeddingSystem e).adjointLift_embedding 0 x

theorem norm_isometry_adjoint_apply_le (e : E →ₗᵢ[ℂ] G) (y : G) :
    ‖(e.toContinuousLinearMap).adjoint y‖ ≤ ‖y‖ :=
  (constantEmbeddingSystem e).norm_adjointLift_apply_le 0 y

omit [CompleteSpace E] in
theorem nonempty_unitSphere_of_finrank_eq_succ (V : Submodule ℂ E) (k : ℕ)
    (hV : Module.finrank ℂ V = k + 1) : Nonempty (UnitSphere (𝕜 := ℂ) V) := by
  have hne : V ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hV
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨⟨⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, V.smul_mem _ hv⟩, by
    simpa using norm_smul_inv_norm (𝕜 := ℂ) hv0⟩⟩

/-- **Courant–Fischer values are invariant under isometric transport** of a positive operator:
`μ_k(e T e^*) = μ_k(T)`. -/
theorem courantValue_isometryConj (e : E →ₗᵢ[ℂ] G) (T : E →L[ℂ] E) (hT : T.IsPositive)
    (k : ℕ) :
    courantValue (e.toContinuousLinearMap ∘L T ∘L (e.toContinuousLinearMap).adjoint) k =
      courantValue T k := by
  set ec : E →L[ℂ] G := e.toContinuousLinearMap with hec
  set S : G →L[ℂ] G := ec ∘L T ∘L ec.adjoint with hS
  have hSpos : S.IsPositive := hT.conj_adjoint ec
  have hSy : ∀ y : G, RCLike.re (inner ℂ (S y) y) = RCLike.re (inner ℂ (T (ec.adjoint y)) (ec.adjoint y)) := by
    intro y
    change RCLike.re (inner ℂ (ec (T (ec.adjoint y))) y) = _
    rw [← ContinuousLinearMap.adjoint_inner_right]
  have hSx : ∀ x : E, RCLike.re (inner ℂ (S (e x)) (e x)) = RCLike.re (inner ℂ (T x) x) := by
    intro x
    rw [hSy]
    change RCLike.re (inner ℂ (T (ec.adjoint (ec x))) (ec.adjoint (ec x))) = _
    rw [show ec.adjoint (ec x) = x from isometry_adjoint_apply_self e x]
  apply le_antisymm
  · -- `μ_k(S) ≤ μ_k(T)`
    refine courantValue_le_of_forall S k (courantValue_nonneg_of_isPositive hT k) ?_
    intro W
    by_cases hinj : ∃ y : G, y ∈ (W : Submodule ℂ G) ∧ ‖y‖ = 1 ∧ ec.adjoint y = 0
    · obtain ⟨y, hyW, hy1, hy0⟩ := hinj
      have h := sphereInf_le_of_mem S (W : Submodule ℂ G) ⟨⟨y, hyW⟩, hy1⟩
      change sphereInf S (W : Submodule ℂ G) ≤ RCLike.re (inner ℂ (S y) y) at h
      rw [hSy] at h
      simp only [hy0, map_zero, inner_zero_left, map_zero] at h
      exact h.trans (courantValue_nonneg_of_isPositive hT k)
    push Not at hinj
    have hinj' : ∀ y ∈ (W : Submodule ℂ G), ec.adjoint y = 0 → y = 0 := by
      intro y hy hy0
      by_contra hne
      have hn : 0 < ‖y‖ := norm_pos_iff.mpr hne
      have hu := hinj (((‖y‖⁻¹ : ℝ) : ℂ) • y) ((W : Submodule ℂ G).smul_mem _ hy)
        (by simpa using norm_smul_inv_norm (𝕜 := ℂ) hne)
      apply hu
      rw [map_smul, hy0, smul_zero]
    set f : (W : Submodule ℂ G) →ₗ[ℂ] E := ec.adjoint.toLinearMap.comp
      (W : Submodule ℂ G).subtype with hf
    have hfinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      exact Subtype.ext (hinj' y y.2 hy)
    set V : Submodule ℂ E := LinearMap.range f with hV
    have hVdim : Module.finrank ℂ V = k + 1 := by
      rw [hV, LinearMap.finrank_range_of_inj hfinj]; exact W.2
    by_cases hs : sphereInf S (W : Submodule ℂ G) ≤ 0
    · exact hs.trans (courantValue_nonneg_of_isPositive hT k)
    push Not at hs
    haveI := nonempty_unitSphere_of_finrank_eq_succ V k hVdim
    refine le_trans ?_ (sphereInf_le_courantValue T k ⟨V, hVdim⟩)
    refine le_ciInf fun x ↦ ?_
    obtain ⟨⟨xv, hxV⟩, hx1⟩ := x
    obtain ⟨y, rfl⟩ := hxV
    change sphereInf S (W : Submodule ℂ G) ≤
      RCLike.re (inner ℂ (T (ec.adjoint (y : G))) (ec.adjoint (y : G)))
    rw [← hSy]
    have hyW : (y : G) ∈ (W : Submodule ℂ G) := y.2
    have hbound : sphereInf S (W : Submodule ℂ G) * ‖(y : G)‖ ^ 2 ≤
        RCLike.re (inner ℂ (S y) (y : G)) := by
      by_cases hy0 : (y : G) = 0
      · rw [hy0]; simp
      have hn : 0 < ‖(y : G)‖ := norm_pos_iff.mpr hy0
      have hu := sphereInf_le_of_mem S (W : Submodule ℂ G)
        ⟨⟨((‖(y : G)‖⁻¹ : ℝ) : ℂ) • (y : G), (W : Submodule ℂ G).smul_mem _ hyW⟩,
          by simpa using norm_smul_inv_norm (𝕜 := ℂ) hy0⟩
      change _ ≤ RCLike.re (inner ℂ (S (((‖(y : G)‖⁻¹ : ℝ) : ℂ) • (y : G)))
        (((‖(y : G)‖⁻¹ : ℝ) : ℂ) • (y : G))) at hu
      rw [show ((‖(y : G)‖⁻¹ : ℝ) : ℂ) = (RCLike.ofReal ‖(y : G)‖⁻¹ : ℂ) from rfl,
        re_inner_apply_self_real_smul] at hu
      have hpos : 0 < ‖(y : G)‖ ^ 2 := by positivity
      calc sphereInf S (W : Submodule ℂ G) * ‖(y : G)‖ ^ 2
          ≤ (‖(y : G)‖⁻¹ ^ 2 * RCLike.re (inner ℂ (S y) (y : G))) * ‖(y : G)‖ ^ 2 := by gcongr
        _ = RCLike.re (inner ℂ (S y) (y : G)) := by field_simp
    have hy1 : 1 ≤ ‖(y : G)‖ := by
      have h := norm_isometry_adjoint_apply_le e (y : G)
      have : ‖ec.adjoint (y : G)‖ = 1 := hx1
      linarith
    have hy1' : 1 ≤ ‖(y : G)‖ ^ 2 := by nlinarith
    nlinarith [hbound, hs]
  · -- `μ_k(T) ≤ μ_k(S)`
    refine courantValue_le_of_forall T k (courantValue_nonneg_of_isPositive hSpos k) ?_
    intro V
    set W : Submodule ℂ G := (V : Submodule ℂ E).map e.toLinearMap with hW
    have hWdim : Module.finrank ℂ W = k + 1 := by
      rw [hW, ← (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective e.toLinearMap e.injective (V : Submodule ℂ E)))]
      exact V.2
    haveI := nonempty_unitSphere_of_finrank_eq_succ W k hWdim
    refine le_trans ?_ (sphereInf_le_courantValue S k ⟨W, hWdim⟩)
    refine le_ciInf fun y ↦ ?_
    obtain ⟨⟨yv, hyW⟩, hy1⟩ := y
    obtain ⟨x, hxV, rfl⟩ := hyW
    change sphereInf T (V : Submodule ℂ E) ≤ RCLike.re (inner ℂ (S (e x)) (e x))
    rw [hSx]
    have hx1 : ‖x‖ = 1 := by
      have : ‖e x‖ = 1 := hy1
      rwa [LinearIsometry.norm_map] at this
    exact sphereInf_le_of_mem T (V : Submodule ℂ E) ⟨⟨x, hxV⟩, hx1⟩

end IsometryConj

section Main

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable {Hlim : Type w'} [NormedAddCommGroup Hlim] [InnerProductSpace ℂ Hlim]
  [CompleteSpace Hlim]

/-- A collectively compact family consists of compact operators. -/
theorem isCompactOperator_of_collectivelyCompact_constant (T : ℕ → H →L[ℂ] H)
    (hcc : (constantSystem ℂ H).CollectivelyCompact T) (n : ℕ) :
    IsCompactOperator (T n) := by
  obtain ⟨C, hC, hsub⟩ := hcc
  refine ⟨C, hC, Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) ?_⟩
  intro x hx
  exact hsub n ⟨x, hx, rfl⟩

/-- **Compact Mosco convergence implies norm-resolvent convergence
(`prop:compact-mosco-resolvent`), general limiting screened space.**  Let the stage forms
`‖A_X u‖²` on `H_X` (weak resolvents `R_X` at a shift `b > 0`) converge in the transported Mosco
sense (`def:transported-mosco`) to the limiting form `‖A u‖²` on a Hilbert space `H_∞` embedded
isometrically by `J_∞` (weak resolvent `R_∞`), with compatibility `P_X → P_∞ = J_∞ J_∞^*`
strongly, and let the family be asymptotically compact (compact graph-screen tail for the stage
graph resolvents).  Then:
* `R_∞` is compact and positive, and `‖J_X R_X J_X^* − J_∞ R_∞ J_∞^*‖ → 0`
  (`eq:norm-resolvent`);
* for every `k`, the intrinsic ordered eigenvalues converge, `μ_k(R_X) → μ_k(R_∞)`, hence
  `λ_{k,X} = μ_k(R_X)⁻¹ − b → λ_{k,∞}` whenever `μ_k(R_∞) > 0` (`eq:eigenvalue-convergence`);
* for every circle avoiding `0` in the resolvent set of `J_∞ R_∞ J_∞^*` (an isolated spectral
  cluster), the transported Riesz projections converge in operator norm, the limiting one has
  finite rank, and the ranks are eventually equal. -/
theorem compactMoscoResolvent_general_exact
    {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Fn : ℕ → Type z} [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
    {Flim : Type*} [NormedAddCommGroup Flim] [InnerProductSpace ℂ Flim]
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (L : System (K := ℂ) (H := WithLp 2 (H × F)) (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Jlim : Hlim →ₗᵢ[ℂ] H)
    (hcompat : ∀ g, Tendsto (fun n ↦ J.rangeProjection n g) atTop
      (𝓝 (transportedLimitOperator Jlim 1 g)))
    (Dn : ∀ n, Submodule ℂ (Hn n)) (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ Hlim) (A : D →ₗ[ℂ] Flim)
    (hmosco : J.TransportedMoscoConverges Jlim
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n)) (ennrealOperatorGraphEnergy D A))
    (b : ℝ) (hb : 0 < b) (Rn : ∀ n, Hn n →L[ℂ] Hn n) (R : Hlim →L[ℂ] Hlim)
    (hstage : ∀ n f, OperatorGraphResolventEquation (Dn n) (An n) b f (Rn n f))
    (hlimit : ∀ f, OperatorGraphResolventEquation D A b f (R f))
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ k, IsCompactOperator (screen k))
    (htail : ∀ ε > 0, ∃ k, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphResolventHilbertGraph (Dn n) (An n) (Rn n) b hb (hstage n)),
      ‖y - screen k y‖ < ε)
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    IsCompactOperator R ∧ R.IsPositive ∧
      Tendsto (J.compressedOperator Rn) atTop (𝓝 (transportedLimitOperator Jlim R)) ∧
      (∀ k : ℕ, Tendsto (fun n ↦ orderedEigenvalue (Rn n) k) atTop
        (𝓝 (orderedEigenvalue R k))) ∧
      (∀ k : ℕ, 0 < orderedEigenvalue R k →
        Tendsto (fun n ↦ (orderedEigenvalue (Rn n) k)⁻¹ - b) atTop
          (𝓝 ((orderedEigenvalue R k)⁻¹ - b))) ∧
      (∀ (center : ℂ) (radius : ℝ), 0 < radius →
        (0 : ℂ) ∉ Metric.closedBall center radius →
        (∀ z ∈ Metric.sphere center radius,
          z ∈ resolventSet ℂ (transportedLimitOperator Jlim R)) →
        Tendsto (fun n ↦ RenewalGeometry.ResolventStability.circleRieszProjection
            (J.compressedOperator Rn n) center radius) atTop
          (𝓝 (RenewalGeometry.ResolventStability.circleRieszProjection
            (transportedLimitOperator Jlim R) center radius)) ∧
        FiniteDimensional ℂ (LinearMap.range
          (RenewalGeometry.ResolventStability.circleRieszProjection
            (transportedLimitOperator Jlim R) center radius).toLinearMap) ∧
        ∀ᶠ n in atTop,
          Module.finrank ℂ (LinearMap.range
            (RenewalGeometry.ResolventStability.circleRieszProjection
              (J.compressedOperator Rn n) center radius).toLinearMap) =
          Module.finrank ℂ (LinearMap.range
            (RenewalGeometry.ResolventStability.circleRieszProjection
              (transportedLimitOperator Jlim R) center radius).toLinearMap)) := by
  have hcc : J.CollectivelyCompact Rn :=
    J.operatorGraphResolvent_collectivelyCompact_of_graphScreenTails L Dn An Rn b hb hstage
      screen hcompact htail hfst
  set T : ℕ → H →L[ℂ] H := J.compressedOperator Rn with hTdef
  set Tlim : H →L[ℂ] H := transportedLimitOperator Jlim R with hTlimdef
  have hTconv : Tendsto T atTop (𝓝 Tlim) :=
    tendsto_compressedOperator_of_transportedMosco J Jlim Dn An D A b hb Rn R hstage hlimit
      hmosco _ hcompat hcc
  have hstageCompact : ∀ n, IsCompactOperator (T n) :=
    isCompactOperator_of_collectivelyCompact_constant T (hcc.compressedOperator J Rn)
  have hstageSymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap :=
    J.compressedOperator_isSymmetric Rn fun n ↦
      operatorGraphResolvent_isSymmetric (Dn n) (An n) b (Rn n) (hstage n)
  have hTlimCompact : IsCompactOperator Tlim :=
    isCompactOperator_of_tendsto hTconv (Eventually.of_forall hstageCompact)
  have hTlimSymm : LinearMap.IsSymmetric Tlim.toLinearMap := by
    apply (constantEmbeddingSystem Jlim).compressedOperator_isSymmetric
    intro _
    exact operatorGraphResolvent_isSymmetric D A b R hlimit
  set Jc : Hlim →L[ℂ] H := Jlim.toContinuousLinearMap with hJc
  have hRpos : R.IsPositive := operatorGraphResolvent_isPositive D A b hb.le R hlimit
  have hRcompact : IsCompactOperator R := by
    have h := (hTlimCompact.comp_clm Jc).clm_comp Jc.adjoint
    have hfun : (Jc.adjoint ∘ (Tlim ∘ Jc) : Hlim → Hlim) = R := by
      funext x
      simp only [Function.comp_apply]
      change Jc.adjoint (Jlim (R (Jc.adjoint (Jlim x)))) = R x
      rw [isometry_adjoint_apply_self Jlim x, isometry_adjoint_apply_self Jlim (R x)]
    rw [hfun] at h
    exact h
  -- intrinsic ordered eigenvalues
  have hstageEig : ∀ n k, orderedEigenvalue (T n) k = orderedEigenvalue (Rn n) k := by
    intro n k
    exact courantValue_isometryConj (J.embedding n) (Rn n)
      (operatorGraphResolvent_isPositive (Dn n) (An n) b hb.le (Rn n) (hstage n)) k
  have hlimEig : ∀ k, orderedEigenvalue Tlim k = orderedEigenvalue R k := by
    intro k
    exact courantValue_isometryConj Jlim R hRpos k
  have heig : ∀ k, Tendsto (fun n ↦ orderedEigenvalue (Rn n) k) atTop
      (𝓝 (orderedEigenvalue R k)) := by
    intro k
    have h := tendsto_orderedEigenvalue hTconv k
    rw [hlimEig] at h
    simpa only [hstageEig] using h
  refine ⟨hRcompact, hRpos, hTconv, heig, ?_, ?_⟩
  · intro k hk
    exact ((heig k).inv₀ hk.ne').sub_const b
  · intro center radius hR hzero hcontour
    obtain ⟨Mb, hMb, hlimitBound⟩ :=
      RenewalGeometry.ResolventStability.exists_circle_resolvent_norm_bound
        Tlim center radius hcontour
    obtain ⟨Nb, -, hstageBound⟩ :=
      RenewalGeometry.ResolventStability.eventually_circle_resolvent_bound_of_tendsto
        T Tlim hTconv center radius Mb hMb hcontour hlimitBound
    have hstageContour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        z ∈ resolventSet ℂ (T n) :=
      hstageBound.mono fun _ hn z hz ↦ (hn z hz).1
    have hQconv := RenewalGeometry.ResolventStability.circleRieszProjection_tendsto hTconv
      center radius hR.le Mb Nb hMb hcontour hlimitBound hstageContour
      (hstageBound.mono fun _ hn z hz ↦ (hn z hz).2)
    haveI hfinLim : FiniteDimensional ℂ (LinearMap.range
        (RenewalGeometry.ResolventStability.circleRieszProjection Tlim center radius).toLinearMap) :=
      RenewalGeometry.ResolventStability.finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
        Tlim hTlimCompact hTlimSymm center radius hR hzero hcontour
    refine ⟨hQconv, hfinLim, ?_⟩
    exact RenewalGeometry.ProjectionStability.eventually_finrank_range_eq_of_tendsto _ _ hQconv
      (hstageContour.mono fun n hn ↦
        RenewalGeometry.ResolventStability.circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
          (T n) (hstageCompact n) (hstageSymm n) center radius hR hn)
      (RenewalGeometry.ResolventStability.circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
        Tlim hTlimCompact hTlimSymm center radius hR hcontour)
      (hstageContour.mono fun n hn ↦
        RenewalGeometry.ResolventStability.finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
          (T n) (hstageCompact n) (hstageSymm n) center radius hR hzero hn)

end Main

/-! ### Non-vacuity: a proper limiting subspace -/

namespace CompactMoscoGeneralWitness

/-- The isometry `(k, f) ↦ (e k, f)` of `L²` products. -/
def prodFstIsometry {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (e : E →ₗᵢ[ℂ] G) : WithLp 2 (E × F) →ₗᵢ[ℂ] WithLp 2 (G × F) where
  toFun y := WithLp.toLp 2 (e y.fst, y.snd)
  map_add' x y := by
    rw [WithLp.add_fst, WithLp.add_snd, map_add, ← WithLp.toLp_add]
    rfl
  map_smul' c x := by
    rw [WithLp.smul_fst, WithLp.smul_snd, map_smul, ← WithLp.toLp_smul]
    rfl
  norm_map' y := by
    have h1 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (e y.fst, y.snd) : WithLp 2 (G × F))
    have h2 := WithLp.prod_norm_sq_eq_of_L2 y
    have h3 : ‖(WithLp.toLp 2 (e y.fst, y.snd) : WithLp 2 (G × F))‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [h1, h2]; simp
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

/-- Weak convergence implies norm convergence in finite dimension. -/
theorem tendsto_of_weak {E : Type*} [NormedAddCommGroup E]
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

/-- Witness carrier `ℂ²`. -/
abbrev Hw := EuclideanSpace ℂ (Fin 2)

theorem norm_e0 : ‖(EuclideanSpace.single 0 1 : Hw)‖ = 1 := by simp

/-- Limit embedding `J_∞ : ℂ → ℂ²`, `z ↦ z e₀`, onto the proper line `ℂ e₀`. -/
def Jlimw : ℂ →ₗᵢ[ℂ] Hw := LinearIsometry.toSpanSingleton ℂ Hw norm_e0

/-- The limiting space is a proper subspace of the carrier. -/
theorem Jlimw_not_surjective : ¬ Function.Surjective Jlimw := by
  intro h
  obtain ⟨z, hz⟩ := h (EuclideanSpace.single 1 1)
  have h1 := congrArg (fun v : Hw ↦ v 1) hz
  simp [Jlimw] at h1

/-- Constant cutoffs equal to the limiting space. -/
def Jw : System (K := ℂ) (H := Hw) (Hn := fun _ : ℕ ↦ ℂ) := constantEmbeddingSystem Jlimw

/-- Graph-space system. -/
def Lw : System (K := ℂ) (H := WithLp 2 (Hw × ℂ)) (Hn := fun _ : ℕ ↦ WithLp 2 (ℂ × ℂ)) :=
  ⟨fun _ ↦ prodFstIsometry Jlimw⟩

/-- Limiting (and cutoff) operator: the identity of `ℂ`. -/
def Aw : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ

/-- The resolvent `(A†A + 1)⁻¹`. -/
def Rw : ℂ →L[ℂ] ℂ := boundedOperatorNormalResolventFamily Aw 1

theorem hstage : ∀ (_ : ℕ) (f : ℂ), OperatorGraphResolventEquation (⊤ : Submodule ℂ ℂ)
    (boundedOperatorGraphMap Aw) 1 f (Rw f) :=
  fun _ f ↦ boundedOperatorNormalResolventFamily_resolventEquation Aw 1 one_pos f

theorem hcompat : ∀ g, Tendsto (fun n ↦ Jw.rangeProjection n g) atTop
    (𝓝 (transportedLimitOperator Jlimw 1 g)) := fun _ ↦ tendsto_const_nhds

theorem hmosco : Jw.TransportedMoscoConverges Jlimw
    (fun _ ↦ ennrealOperatorGraphEnergy (⊤ : Submodule ℂ ℂ) (boundedOperatorGraphMap Aw))
    (ennrealOperatorGraphEnergy (⊤ : Submodule ℂ ℂ) (boundedOperatorGraphMap Aw)) := by
  have hcont := continuous_ennrealBoundedOperatorEnergy Aw
  simp only [ennrealOperatorGraphEnergy_top]
  constructor
  · intro x B hx
    set A0 : ℂ := (Jlimw.toContinuousLinearMap).adjoint B with hA0
    have hweak : ∀ z : ℂ, Tendsto (fun n ↦ inner ℂ (x n) z) atTop (𝓝 (inner ℂ A0 z)) := by
      intro z
      have h := hx (Jlimw z)
      have e1 : ∀ n, inner ℂ (Jw.embedding n (x n)) (Jlimw z) = inner ℂ (x n) z := fun n ↦
        LinearIsometry.inner_map_map Jlimw (x n) z
      have e2 : inner ℂ B (Jlimw z) = inner ℂ A0 z := by
        rw [hA0, ContinuousLinearMap.adjoint_inner_left]
        rfl
      simp only [e1, e2] at h
      exact h
    have hs : Tendsto x atTop (𝓝 A0) := tendsto_of_weak x A0 hweak
    have hJs : Jw.StronglyConverges x (Jlimw A0) :=
      (Jlimw.continuous.tendsto A0).comp hs
    have hB : Jlimw A0 = B := Jw.weaklyConverges_unique hJs.weak hx
    exact ⟨A0, hB, ((hcont.tendsto A0).comp hs).liminf_eq.ge⟩
  · intro A _
    exact ⟨fun _ ↦ A, tendsto_const_nhds, tendsto_const_nhds⟩

/-- Identity screens (compact: finite dimension). -/
def screenW : ℕ → WithLp 2 (Hw × ℂ) →L[ℂ] WithLp 2 (Hw × ℂ) :=
  fun _ ↦ ContinuousLinearMap.id ℂ _

theorem hcompact : ∀ k, IsCompactOperator (screenW k) := fun _ ↦
  ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩

theorem hfst : ∀ (n : ℕ) (y : WithLp 2 (ℂ × ℂ)), Jw.embedding n y.fst = (Lw.embedding n y).fst :=
  fun _ _ ↦ rfl

/-- **Non-vacuity of the general `prop:compact-mosco-resolvent` packet with a proper limiting
subspace** `H_∞ = ℂ ↪ ℂ²` (the line `ℂ e₀`): all hypotheses of
`compactMoscoResolvent_general_exact` hold, and the theorem yields norm-resolvent convergence
onto `J_∞ R_∞ J_∞^*`. -/
theorem compactMoscoResolvent_general_nonvacuous :
    ¬ Function.Surjective Jlimw ∧ Tendsto (Jw.compressedOperator (fun _ ↦ Rw)) atTop
      (𝓝 (transportedLimitOperator Jlimw Rw)) := by
  obtain ⟨-, -, hT, -⟩ := compactMoscoResolvent_general_exact (Fn := fun _ ↦ ℂ) Jw Lw Jlimw
    hcompat (fun _ ↦ ⊤) (fun _ ↦ boundedOperatorGraphMap Aw) ⊤ (boundedOperatorGraphMap Aw)
    hmosco 1 one_pos (fun _ ↦ Rw) Rw hstage (hstage 0) screenW hcompact
    (fun ε hε ↦ ⟨0, fun y _ ↦ by simp [screenW, hε]⟩) hfst
  exact ⟨Jlimw_not_surjective, hT⟩

end CompactMoscoGeneralWitness

end RenewalGeometry.VaryingHilbert.System
