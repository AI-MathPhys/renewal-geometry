/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.TransportedMoscoAsymptoticCompactness
import RenewalGeometry.OperatorLimits.ENNRealOperatorGraphResolventMinimizer
import RenewalGeometry.OperatorLimits.VaryingHilbertFiniteStageCompression
import RenewalGeometry.OperatorLimits.VaryingHilbertCollectiveCompactness
import RenewalGeometry.OperatorLimits.CompressedOperatorNormConvergence
import RenewalGeometry.OperatorLimits.CollectivelyCompactLimit
import RenewalGeometry.OperatorLimits.OperatorGraphResolventDenseRange
import RenewalGeometry.OperatorLimits.VaryingHilbertResolventObjective

/-!
# Transported Mosco convergence with a general limiting space: resolvent convergence

Covers the resolvent mechanism of `prop:compact-mosco-resolvent` /
`lem:mosco-strong-resolvent` of the spacetime–gauge duality manuscript **with an explicit
limiting screened space** `H_∞` embedded isometrically by `J_∞ : H_∞ → ℋ` (possibly a proper
subspace of the common carrier), in the transported Mosco sense `def:transported-mosco`
(`System.TransportedMoscoConverges`), under the standing compatibility `P_X → P_∞` strongly.

* `TransportedMoscoConverges.exists_of_strictMono_strong`: (M1) along a strictly increasing
  subsequence for strongly convergent transported vectors (the subsequence is filled up by the
  transported compressions `J_X^* y`, which converge to `y` by compatibility).
* `tendsto_compressedOperator_apply_of_transportedMosco` (`lem:mosco-strong-resolvent`):
  for graph forms with weak resolvent equations and collectively compact stage resolvents,
  `J_X R_X J_X^* f → J_∞ R_∞ J_∞^* f` for every `f`.
* `tendsto_compressedOperator_of_transportedMosco` (`eq:norm-resolvent`): the convergence holds
  in operator norm (`lem:collective-norm`).
-/

open Filter Topology
open scoped ENNReal

noncomputable section

namespace RenewalGeometry.VaryingHilbert.System

universe u v w w'

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable {Hlim : Type w'} [NormedAddCommGroup Hlim] [InnerProductSpace ℂ Hlim]
  [CompleteSpace Hlim]

/-- The transported limit operator `J_∞ T J_∞^*` on the common carrier. -/
def transportedLimitOperator (Jlim : Hlim →ₗᵢ[ℂ] H) (T : Hlim →L[ℂ] Hlim) : H →L[ℂ] H :=
  (constantEmbeddingSystem Jlim).compressedOperator (fun _ ↦ T) 0

theorem transportedLimitOperator_apply (Jlim : Hlim →ₗᵢ[ℂ] H) (T : Hlim →L[ℂ] Hlim) (f : H) :
    transportedLimitOperator Jlim T f =
      Jlim (T ((Jlim.toContinuousLinearMap).adjoint f)) := rfl

/-- The adjoint of a stage embedding is a contraction. -/
theorem norm_adjointLift_apply_le (J : System (K := ℂ) (H := H) (Hn := Hn)) (n : ℕ) (x : H) :
    ‖J.adjointLift n x‖ ≤ ‖x‖ := by
  let e : Hn n →L[ℂ] H := (J.embedding n).toContinuousLinearMap
  calc ‖J.adjointLift n x‖ = ‖e.adjoint x‖ := rfl
    _ ≤ ‖e.adjoint‖ * ‖x‖ := (e.adjoint).le_opNorm x
    _ = ‖e‖ * ‖x‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * ‖x‖ := by gcongr; exact (J.embedding n).norm_toContinuousLinearMap_le
    _ = ‖x‖ := one_mul _

theorem rangeProjection_apply_eq (J : System (K := ℂ) (H := H) (Hn := Hn)) (n : ℕ) (x : H) :
    J.rangeProjection n x = J.embedding n (J.adjointLift n x) := rfl

theorem norm_rangeProjection_apply_le (J : System (K := ℂ) (H := H) (Hn := Hn)) (n : ℕ)
    (x : H) : ‖J.rangeProjection n x‖ ≤ ‖x‖ := by
  rw [rangeProjection_apply_eq, LinearIsometry.norm_map]
  exact J.norm_adjointLift_apply_le n x

omit [CompleteSpace Hlim] in
/-- **(M1) along strictly increasing subsequences.**  Under transported Mosco convergence and the
compatibility `P_X → P_∞` strongly, a strongly convergent transported subsequence has its limit
in `J_∞ H_∞`, and the limit form is bounded by the liminf of the subsequence energies. -/
theorem TransportedMoscoConverges.exists_of_strictMono_strong
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    {Jlim : Hlim →ₗᵢ[ℂ] H} {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : Hlim → ℝ≥0∞}
    (h : J.TransportedMoscoConverges Jlim q qlim)
    (Pinf : H →L[ℂ] H)
    (hcompat : ∀ g, Tendsto (fun n ↦ J.rangeProjection n g) atTop (𝓝 (Pinf g)))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (z : ∀ k, Hn (ψ k)) {y : H}
    (hz : Tendsto (fun k ↦ J.embedding (ψ k) (z k)) atTop (𝓝 y)) :
    ∃ A : Hlim, Jlim A = y ∧ qlim A ≤ liminf (fun k ↦ q (ψ k) (z k)) atTop := by
  classical
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  -- `y` is fixed by the limiting projection
  have hPy : Tendsto (fun k ↦ J.rangeProjection (ψ k) y) atTop (𝓝 y) := by
    have hdiff : Tendsto (fun k ↦ J.rangeProjection (ψ k) y - J.embedding (ψ k) (z k))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hz0 : Tendsto (fun k ↦ ‖y - J.embedding (ψ k) (z k)‖) atTop (𝓝 0) := by
        have := (tendsto_iff_norm_sub_tendsto_zero.mp hz)
        simpa only [norm_sub_rev] using this
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hz0
      have hfix : J.rangeProjection (ψ k) (J.embedding (ψ k) (z k)) =
          J.embedding (ψ k) (z k) := by
        rw [rangeProjection_apply_eq, adjointLift_embedding]
      calc ‖J.rangeProjection (ψ k) y - J.embedding (ψ k) (z k)‖
          = ‖J.rangeProjection (ψ k) (y - J.embedding (ψ k) (z k))‖ := by
            rw [map_sub, hfix]
        _ ≤ ‖y - J.embedding (ψ k) (z k)‖ := J.norm_rangeProjection_apply_le _ _
    simpa using hdiff.add hz
  have hyfix : Pinf y = y := tendsto_nhds_unique ((hcompat y).comp hψt) hPy
  -- fill the subsequence up to a full sequence
  let w : ℕ → H := fun n ↦
    if hn : ∃ k, ψ k = n then J.embedding (ψ hn.choose) (z hn.choose) else y
  let x : ∀ n, Hn n := fun n ↦ J.adjointLift n (w n)
  have hwψ : ∀ k, w (ψ k) = J.embedding (ψ k) (z k) := by
    intro k
    have hex : ∃ k', ψ k' = ψ k := ⟨k, rfl⟩
    have hch : hex.choose = k := hψ.injective hex.choose_spec
    have key : ∀ j, j = k → J.embedding (ψ j) (z j) = J.embedding (ψ k) (z k) := by
      rintro j rfl; rfl
    simp only [w, dif_pos hex]
    exact key _ hch
  have hxψ : ∀ k, x (ψ k) = z k := by
    intro k
    simp only [x, hwψ k, adjointLift_embedding]
  have hw : Tendsto w atTop (𝓝 y) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hz ε hε
    refine ⟨ψ K, fun n hn ↦ ?_⟩
    by_cases hex : ∃ k, ψ k = n
    · have hspec := hex.choose_spec
      have hge : K ≤ hex.choose := by
        rw [← hψ.le_iff_le, hspec]; exact hn
      simp only [w, dif_pos hex]
      exact hK _ hge
    · simp only [w, dif_neg hex, dist_self]; exact hε
  have hxstrong : J.StronglyConverges x y := by
    unfold StronglyConverges
    have h1 : Tendsto (fun n ↦ J.rangeProjection n (w n - y)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun n ↦ J.norm_rangeProjection_apply_le n _) ?_
      have := (tendsto_iff_norm_sub_tendsto_zero.mp hw)
      exact this
    have h2 : Tendsto (fun n ↦ J.rangeProjection n y) atTop (𝓝 y) := by
      have := hcompat y; rwa [hyfix] at this
    have h3 := h1.add h2
    simp only [zero_add, map_sub, sub_add_cancel] at h3
    exact h3
  obtain ⟨A, hA, hle⟩ := h.weak_liminf x y hxstrong.weak
  refine ⟨A, hA, hle.trans ?_⟩
  have hcomp : liminf (fun n ↦ q n (x n)) atTop ≤
      liminf (fun n ↦ q n (x n)) (map ψ atTop) :=
    liminf_le_liminf_of_le hψt
  rw [← liminf_comp] at hcomp
  refine hcomp.trans (le_of_eq ?_)
  congr 1
  funext k
  simp only [Function.comp_apply, hxψ k]

/-- The graph energy on its domain. -/
theorem ennrealOperatorGraphEnergy_of_mem {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] G) {x : E} (hx : x ∈ D) :
    ennrealOperatorGraphEnergy D A x = ENNReal.ofReal (‖A ⟨x, hx⟩‖ ^ 2) := by
  classical
  rw [ennrealOperatorGraphEnergy, dif_pos hx]

/-- The graph energy off its domain. -/
theorem ennrealOperatorGraphEnergy_of_not_mem {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] G) {x : E} (hx : x ∉ D) :
    ennrealOperatorGraphEnergy D A x = ∞ := by
  classical
  rw [ennrealOperatorGraphEnergy, dif_neg hx]

/-- **Strong transported resolvent convergence (`lem:mosco-strong-resolvent`).**  Let the stage
graph forms `‖A_X u‖²` (weak resolvents `R_X` at shift `b`) converge in the transported Mosco
sense to the limiting graph form `‖A u‖²` on `H_∞` (weak resolvent `R`), with compatibility
`P_X → P_∞` strongly and collectively compact stage resolvents.  Then for every `f`,
`J_X R_X J_X^* f → J_∞ R J_∞^* f`. -/
theorem tendsto_compressedOperator_apply_of_transportedMosco
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {Fn : ℕ → Type*} [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
    (J : System (K := ℂ) (H := H) (Hn := Hn)) (Jlim : Hlim →ₗᵢ[ℂ] H)
    (Dn : ∀ n, Submodule ℂ (Hn n)) (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ Hlim) (A : D →ₗ[ℂ] F)
    (b : ℝ) (hb : 0 < b) (Rn : ∀ n, Hn n →L[ℂ] Hn n) (R : Hlim →L[ℂ] Hlim)
    (hstage : ∀ n g, OperatorGraphResolventEquation (Dn n) (An n) b g (Rn n g))
    (hlimit : ∀ g, OperatorGraphResolventEquation D A b g (R g))
    (hmosco : J.TransportedMoscoConverges Jlim
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n)) (ennrealOperatorGraphEnergy D A))
    (Pinf : H →L[ℂ] H)
    (hcompat : ∀ g, Tendsto (fun n ↦ J.rangeProjection n g) atTop (𝓝 (Pinf g)))
    (hcc : J.CollectivelyCompact Rn) (f : H) :
    Tendsto (fun n ↦ J.compressedOperator Rn n f) atTop
      (𝓝 (transportedLimitOperator Jlim R f)) := by
  classical
  set Jc : Hlim →L[ℂ] H := Jlim.toContinuousLinearMap with hJc
  set g : Hlim := Jc.adjoint f with hg
  set ustar : Hlim := R g with hustar
  obtain ⟨C, hC, hCsub⟩ := hcc
  set Kset : Set H := (fun v ↦ ((‖f‖ : ℝ) : ℂ) • v) '' C with hKset
  have hK : IsCompact Kset := hC.image (continuous_const_smul _)
  have hmem : ∀ n, J.compressedOperator Rn n f ∈ Kset := by
    intro n
    by_cases hf : f = 0
    · refine ⟨J.embeddedOperator Rn n 0, hCsub n ⟨0, by simp, rfl⟩, ?_⟩
      rw [hf, map_zero]
      simp
    · have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
      set v : Hn n := (((‖f‖ : ℝ) : ℂ)⁻¹) • J.adjointLift n f with hv
      have hvn : ‖v‖ ≤ 1 := by
        rw [hv, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfpos]
        calc ‖f‖⁻¹ * ‖J.adjointLift n f‖ ≤ ‖f‖⁻¹ * ‖f‖ := by
              gcongr; exact J.norm_adjointLift_apply_le n f
          _ = 1 := inv_mul_cancel₀ hfpos.ne'
      refine ⟨J.embeddedOperator Rn n v, hCsub n ⟨v, mem_closedBall_zero_iff.mpr hvn, rfl⟩, ?_⟩
      change ((‖f‖ : ℝ) : ℂ) • J.embedding n (Rn n v) = J.embedding n (Rn n (J.adjointLift n f))
      have hne : ((‖f‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hfpos.ne'
      rw [← map_smul, ← map_smul, hv, smul_smul, mul_inv_cancel₀ hne, one_smul]
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, -, hφns⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨y, -, φ', hφ', hy⟩ := hK.tendsto_subseq (fun k ↦ hmem (ns (φ k)))
  refine ⟨φ ∘ φ', ?_⟩
  set ψ : ℕ → ℕ := ns ∘ φ ∘ φ' with hψdef
  have hψ : StrictMono ψ := hφns.comp hφ'
  let u : ∀ k, Hn (ψ k) := fun k ↦ Rn (ψ k) (J.adjointLift (ψ k) f)
  have hu : Tendsto (fun k ↦ J.embedding (ψ k) (u k)) atTop (𝓝 y) := hy
  suffices hyt : transportedLimitOperator Jlim R f = y by
    rw [hyt]; exact hy
  obtain ⟨A0, hA0, hle⟩ :=
    TransportedMoscoConverges.exists_of_strictMono_strong J hmosco Pinf hcompat hψ u hu
  have hmemu : ∀ k, u k ∈ Dn (ψ k) := fun k ↦ (hstage (ψ k) _).mem
  have hinnerJ : ∀ (n : ℕ) (x : Hn n),
      inner ℂ x (J.adjointLift n f) = inner ℂ (J.embedding n x) f := by
    intro n x
    exact ContinuousLinearMap.adjoint_inner_right _ x f
  have hinnerLim : ∀ x : Hlim, inner ℂ x g = inner ℂ (Jlim x) f := by
    intro x
    exact ContinuousLinearMap.adjoint_inner_right _ x f
  have heul : ∀ k, ‖An (ψ k) ⟨u k, hmemu k⟩‖ ^ 2 + b * ‖u k‖ ^ 2 =
      (inner ℂ (J.embedding (ψ k) (u k)) f).re := by
    intro k
    have E := (hstage (ψ k) (J.adjointLift (ψ k) f)).weakEuler ⟨u k, hmemu k⟩
    change RCLike.re (inner ℂ (An (ψ k) ⟨u k, hmemu k⟩) (An (ψ k) ⟨u k, hmemu k⟩)) +
        b * RCLike.re (inner ℂ (u k) (u k)) =
      RCLike.re (inner ℂ (u k) (J.adjointLift (ψ k) f)) at E
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq, hinnerJ] at E
    exact E
  set c : ℝ := (inner ℂ y f).re - b * ‖y‖ ^ 2 with hcdef
  have hqk : Tendsto (fun k ↦ ‖An (ψ k) ⟨u k, hmemu k⟩‖ ^ 2) atTop (𝓝 c) := by
    have hfun : (fun k ↦ ‖An (ψ k) ⟨u k, hmemu k⟩‖ ^ 2) = fun k ↦
        (inner ℂ (J.embedding (ψ k) (u k)) f).re - b * ‖J.embedding (ψ k) (u k)‖ ^ 2 := by
      funext k; rw [LinearIsometry.norm_map, ← heul k]; ring
    rw [hfun]
    exact ((Complex.continuous_re.tendsto _).comp (hu.inner tendsto_const_nhds)).sub
      ((hu.norm.pow 2).const_mul b)
  have hc0 : 0 ≤ c := ge_of_tendsto' hqk (fun k ↦ sq_nonneg _)
  have hliminf : liminf (fun k ↦ ennrealOperatorGraphEnergy (Dn (ψ k)) (An (ψ k)) (u k)) atTop =
      ENNReal.ofReal c := by
    have hfun : (fun k ↦ ennrealOperatorGraphEnergy (Dn (ψ k)) (An (ψ k)) (u k)) =
        fun k ↦ ENNReal.ofReal (‖An (ψ k) ⟨u k, hmemu k⟩‖ ^ 2) := by
      funext k; exact ennrealOperatorGraphEnergy_of_mem _ _ (hmemu k)
    rw [hfun]
    exact (ENNReal.tendsto_ofReal hqk).liminf_eq
  rw [hliminf] at hle
  have hA0D : A0 ∈ D := by
    by_contra hnot
    rw [ennrealOperatorGraphEnergy_of_not_mem D A hnot, top_le_iff] at hle
    exact ENNReal.ofReal_ne_top hle
  have hAA0 : ‖A ⟨A0, hA0D⟩‖ ^ 2 ≤ c := by
    rw [ennrealOperatorGraphEnergy_of_mem D A hA0D, ENNReal.ofReal_le_ofReal_iff hc0] at hle
    exact hle
  -- recovery sequence for the limit minimiser
  have hustarD : ustar ∈ D := (hlimit g).mem
  obtain ⟨wseq, hwJ, hwq, hwfin⟩ :=
    TransportedMoscoConverges.recovery_eventually_finite J hmosco ustar
      (by rw [ennrealOperatorGraphEnergy_of_mem D A hustarD]; exact ENNReal.ofReal_ne_top)
  have hwJ' : Tendsto (fun n ↦ J.embedding n (wseq n)) atTop (𝓝 (Jlim ustar)) := hwJ
  set Lstar : ℝ := ‖A ⟨ustar, hustarD⟩‖ ^ 2 + b * ‖ustar‖ ^ 2 - 2 * (inner ℂ (Jlim ustar) f).re
    with hLstar
  have hObjw : Tendsto (fun n ↦ (ennrealOperatorGraphEnergy (Dn n) (An n) (wseq n)).toReal +
      b * ‖wseq n‖ ^ 2 - 2 * (inner ℂ (J.embedding n (wseq n)) f).re) atTop (𝓝 Lstar) := by
    have h1 := (ENNReal.tendsto_toReal (by
      rw [ennrealOperatorGraphEnergy_of_mem D A hustarD]; exact ENNReal.ofReal_ne_top)).comp hwq
    rw [ennrealOperatorGraphEnergy_of_mem D A hustarD,
      ENNReal.toReal_ofReal (sq_nonneg _)] at h1
    have h2 : Tendsto (fun n ↦ ‖wseq n‖) atTop (𝓝 ‖ustar‖) := by
      have := hwJ'.norm
      simpa only [LinearIsometry.norm_map] using this
    have h3 := (Complex.continuous_re.tendsto _).comp (hwJ'.inner (tendsto_const_nhds (x := f)))
    exact (h1.add ((h2.pow 2).const_mul b)).sub (h3.const_mul 2)
  have hObju : ∀ k, (ennrealOperatorGraphEnergy (Dn (ψ k)) (An (ψ k)) (u k)).toReal +
      b * ‖u k‖ ^ 2 - 2 * (inner ℂ (J.embedding (ψ k) (u k)) f).re =
        -(inner ℂ (J.embedding (ψ k) (u k)) f).re := by
    intro k
    rw [ennrealOperatorGraphEnergy_of_mem _ _ (hmemu k), ENNReal.toReal_ofReal (sq_nonneg _)]
    linarith [heul k]
  have hminimal : ∀ᶠ k in atTop,
      -(inner ℂ (J.embedding (ψ k) (u k)) f).re ≤
        (ennrealOperatorGraphEnergy (Dn (ψ k)) (An (ψ k)) (wseq (ψ k))).toReal +
          b * ‖wseq (ψ k)‖ ^ 2 - 2 * (inner ℂ (J.embedding (ψ k) (wseq (ψ k))) f).re := by
    filter_upwards [hψ.tendsto_atTop.eventually hwfin] with k hk
    have hwD : wseq (ψ k) ∈ Dn (ψ k) :=
      (ennrealOperatorGraphEnergy_ne_top_iff _ _ _).mp hk
    have hmin := operatorGraph_resolventObjective_minimizer (Dn (ψ k)) (An (ψ k)) b hb.le
      (J.adjointLift (ψ k) f) (u k) (hstage (ψ k) _) (wseq (ψ k)) hwD
    simp only [resolventObjective] at hmin
    change _ + _ - 2 * RCLike.re (inner ℂ (u k) (J.adjointLift (ψ k) f)) ≤
      _ + _ - 2 * RCLike.re (inner ℂ (wseq (ψ k)) (J.adjointLift (ψ k) f)) at hmin
    rw [hinnerJ, hinnerJ] at hmin
    rw [← hObju k]
    exact hmin
  have hlimu : Tendsto (fun k ↦ -(inner ℂ (J.embedding (ψ k) (u k)) f).re) atTop
      (𝓝 (-(inner ℂ y f).re)) :=
    ((Complex.continuous_re.tendsto _).comp (hu.inner tendsto_const_nhds)).neg
  have hle2 : -(inner ℂ y f).re ≤ Lstar :=
    le_of_tendsto_of_tendsto hlimu (hObjw.comp hψ.tendsto_atTop) hminimal
  -- compare the limit objectives
  have hgap := operatorGraph_resolventObjective_sub_eq D A b g ustar (hlimit g) A0 hA0D
  simp only [resolventObjective] at hgap
  change _ + _ - 2 * RCLike.re (inner ℂ A0 g) - (_ + _ - 2 * RCLike.re (inner ℂ ustar g)) = _
    at hgap
  rw [ennrealOperatorGraphEnergy_of_mem D A hA0D, ennrealOperatorGraphEnergy_of_mem D A hustarD,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _),
    hinnerLim, hinnerLim, hA0] at hgap
  have hnormA0 : ‖A0‖ = ‖y‖ := by rw [← hA0, LinearIsometry.norm_map]
  rw [hnormA0] at hgap
  have hsq : b * ‖A0 - ustar‖ ^ 2 ≤ 0 := by
    change _ = _ at hgap
    simp only [RCLike.re_to_complex] at hgap
    nlinarith [sq_nonneg ‖A ⟨A0, hA0D⟩ - A ⟨ustar, hustarD⟩‖]
  have hzero : ‖A0 - ustar‖ ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right hsq hb) (sq_nonneg _)
  have hA0eq : A0 = ustar :=
    sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hzero))
  rw [transportedLimitOperator_apply, ← hA0, hA0eq]

/-- **Norm-resolvent convergence (`eq:norm-resolvent`) with a general limiting space.** -/
theorem tendsto_compressedOperator_of_transportedMosco
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {Fn : ℕ → Type*} [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
    (J : System (K := ℂ) (H := H) (Hn := Hn)) (Jlim : Hlim →ₗᵢ[ℂ] H)
    (Dn : ∀ n, Submodule ℂ (Hn n)) (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ Hlim) (A : D →ₗ[ℂ] F)
    (b : ℝ) (hb : 0 < b) (Rn : ∀ n, Hn n →L[ℂ] Hn n) (R : Hlim →L[ℂ] Hlim)
    (hstage : ∀ n g, OperatorGraphResolventEquation (Dn n) (An n) b g (Rn n g))
    (hlimit : ∀ g, OperatorGraphResolventEquation D A b g (R g))
    (hmosco : J.TransportedMoscoConverges Jlim
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n)) (ennrealOperatorGraphEnergy D A))
    (Pinf : H →L[ℂ] H)
    (hcompat : ∀ g, Tendsto (fun n ↦ J.rangeProjection n g) atTop (𝓝 (Pinf g)))
    (hcc : J.CollectivelyCompact Rn) :
    Tendsto (J.compressedOperator Rn) atTop (𝓝 (transportedLimitOperator Jlim R)) := by
  have hstrong := tendsto_compressedOperator_apply_of_transportedMosco J Jlim Dn An D A b hb Rn R
    hstage hlimit hmosco Pinf hcompat hcc
  have hsymm : ∀ n, LinearMap.IsSymmetric (Rn n).toLinearMap := fun n ↦
    operatorGraphResolvent_isSymmetric (Dn n) (An n) b (Rn n) (hstage n)
  have hlimSymm : LinearMap.IsSymmetric (transportedLimitOperator Jlim R).toLinearMap := by
    apply (constantEmbeddingSystem Jlim).compressedOperator_isSymmetric
    intro _
    exact operatorGraphResolvent_isSymmetric D A b R hlimit
  exact tendsto_operatorNorm_of_collectivelyCompact_of_symmetric'
    (J.compressedOperator Rn) _ (hcc.compressedOperator J Rn)
    (J.compressedOperator_isSymmetric Rn hsymm) hlimSymm hstrong

end RenewalGeometry.VaryingHilbert.System
