/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.TransportedMoscoStrongResolventConvergence
import RenewalGeometry.OperatorLimits.VaryingHilbertWeakSubsequenceCompactness
import RenewalGeometry.OperatorLimits.OperatorGraphResolventBound
import RenewalGeometry.OperatorLimits.CompactMoscoResolventGeneralExact

/-!
# Transported Mosco convergence gives strong transported resolvents, without compactness

Covers `lem:mosco-strong-resolvent` of the spacetime–gauge duality manuscript exactly as stated:
under transported Mosco convergence (`def:transported-mosco`, `System.TransportedMoscoConverges`)
of the stage forms to a limiting form on a limiting Hilbert space `H_∞` embedded isometrically
by `J_∞` (possibly a proper subspace of the separable common carrier `ℋ`), together with the
standing compatibility `P_X → P_∞` strongly, for every fixed `f`
`J_X (𝓛_X + b)⁻¹ J_X^* f → J_∞ (𝓛_∞ + b)⁻¹ J_∞^* f` strongly.  **No compactness hypothesis**
is used: the proof follows the paper (weak subsequence extraction in the separable Hilbert
carrier, Mosco liminf along subsequences, recovery sequences plus stage minimality, strict
convexity of the limiting objective, and convergence of the Hilbert norms).

* `rangeProjection_inner_symm`, `limitProjection_inner_symm`: the stage range projections are
  symmetric, hence so is any strong limit `P_∞`.
* `TransportedMoscoConverges.exists_of_strictMono_weak`: (M1) along strictly increasing
  subsequences for **weakly** convergent bounded transported vectors (the gaps are filled by
  `J_X^* y`, using `P_∞ y = y`, which follows from compatibility).
* `tendsto_compressedOperator_apply_of_transportedMosco_weak` (`lem:mosco-strong-resolvent`).
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

/-- The stage range projections `P_X = J_X J_X^*` are symmetric. -/
theorem rangeProjection_inner_symm (J : System (K := ℂ) (H := H) (Hn := Hn)) (n : ℕ)
    (g h : H) :
    inner ℂ (J.rangeProjection n g) h = inner ℂ g (J.rangeProjection n h) := by
  let e : Hn n →L[ℂ] H := (J.embedding n).toContinuousLinearMap
  change inner ℂ (e (e.adjoint g)) h = inner ℂ g (e (e.adjoint h))
  rw [← ContinuousLinearMap.adjoint_inner_right e (e.adjoint g) h,
    ContinuousLinearMap.adjoint_inner_left]

/-- A strong limit `P_∞` of the stage range projections is symmetric. -/
theorem limitProjection_inner_symm (J : System (K := ℂ) (H := H) (Hn := Hn)) (Pinf : H →L[ℂ] H)
    (hcompat : ∀ g, Tendsto (fun n ↦ J.rangeProjection n g) atTop (𝓝 (Pinf g))) (g h : H) :
    inner ℂ (Pinf g) h = inner ℂ g (Pinf h) := by
  have h1 : Tendsto (fun n ↦ inner ℂ (J.rangeProjection n g) h) atTop
      (𝓝 (inner ℂ (Pinf g) h)) := (hcompat g).inner tendsto_const_nhds
  have h2 : Tendsto (fun n ↦ inner ℂ (J.rangeProjection n g) h) atTop
      (𝓝 (inner ℂ g (Pinf h))) := by
    simp_rw [rangeProjection_inner_symm]
    exact tendsto_const_nhds.inner (hcompat h)
  exact tendsto_nhds_unique h1 h2

omit [CompleteSpace Hlim] in
/-- **(M1) along strictly increasing subsequences, weak form.**  Under transported Mosco
convergence and the compatibility `P_X → P_∞` strongly, a bounded transported subsequence
converging weakly to `y` has `y = J_∞ A` with `q_∞(A)` at most the liminf of the subsequence
energies. -/
theorem TransportedMoscoConverges.exists_of_strictMono_weak
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    {Jlim : Hlim →ₗᵢ[ℂ] H} {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : Hlim → ℝ≥0∞}
    (h : J.TransportedMoscoConverges Jlim q qlim)
    (Pinf : H →L[ℂ] H)
    (hcompat : ∀ g, Tendsto (fun n ↦ J.rangeProjection n g) atTop (𝓝 (Pinf g)))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (z : ∀ k, Hn (ψ k)) (C : ℝ)
    (hC : ∀ k, ‖J.embedding (ψ k) (z k)‖ ≤ C) {y : H}
    (hz : ∀ g, Tendsto (fun k ↦ inner ℂ (J.embedding (ψ k) (z k)) g) atTop
      (𝓝 (inner ℂ y g))) :
    ∃ A : Hlim, Jlim A = y ∧ qlim A ≤ liminf (fun k ↦ q (ψ k) (z k)) atTop := by
  classical
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  -- `P_∞ y = y`
  have hfixP : ∀ k, J.rangeProjection (ψ k) (J.embedding (ψ k) (z k)) = J.embedding (ψ k) (z k) :=
    fun k ↦ by rw [rangeProjection_apply_eq, adjointLift_embedding]
  have hyP : ∀ g, inner ℂ y g = inner ℂ y (Pinf g) := by
    intro g
    have hdiff : Tendsto (fun k ↦ inner ℂ (J.embedding (ψ k) (z k))
        (J.rangeProjection (ψ k) g - Pinf g)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hP : Tendsto (fun k ↦ ‖J.rangeProjection (ψ k) g - Pinf g‖) atTop (𝓝 0) :=
        (tendsto_iff_norm_sub_tendsto_zero.mp (hcompat g)).comp hψt
      have hCP : Tendsto (fun k ↦ C * ‖J.rangeProjection (ψ k) g - Pinf g‖) atTop (𝓝 0) := by
        simpa using hP.const_mul C
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hCP
      calc ‖inner ℂ (J.embedding (ψ k) (z k)) (J.rangeProjection (ψ k) g - Pinf g)‖
          ≤ ‖J.embedding (ψ k) (z k)‖ * ‖J.rangeProjection (ψ k) g - Pinf g‖ :=
            norm_inner_le_norm _ _
        _ ≤ C * ‖J.rangeProjection (ψ k) g - Pinf g‖ := by gcongr; exact hC k
    have hsum := hdiff.add (hz (Pinf g))
    simp only [inner_sub_right, sub_add_cancel, zero_add] at hsum
    have heq : (fun k ↦ inner ℂ (J.embedding (ψ k) (z k)) (J.rangeProjection (ψ k) g)) =
        fun k ↦ inner ℂ (J.embedding (ψ k) (z k)) g := by
      funext k
      rw [← rangeProjection_inner_symm, hfixP]
    rw [heq] at hsum
    exact tendsto_nhds_unique (hz g) hsum
  have hyfix : Pinf y = y := by
    apply ext_inner_right ℂ
    intro g
    rw [limitProjection_inner_symm J Pinf hcompat, ← hyP]
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
  have hxgap : ∀ n, (¬ ∃ k, ψ k = n) → J.embedding n (x n) = J.rangeProjection n y := by
    intro n hn
    simp only [x, w, dif_neg hn]
    rfl
  have hweak : J.WeaklyConverges x y := by
    intro g
    have hgapT : Tendsto (fun n ↦ inner ℂ (J.rangeProjection n y) g) atTop
        (𝓝 (inner ℂ y g)) := by
      have := Filter.Tendsto.inner (𝕜 := ℂ) (hcompat y) (tendsto_const_nhds (x := g))
      rwa [hyfix] at this
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp (hz g) ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hgapT ε hε
    refine ⟨max (ψ K) N, fun n hn ↦ ?_⟩
    by_cases hex : ∃ k, ψ k = n
    · obtain ⟨k, rfl⟩ := hex
      rw [hxψ k]
      exact hK k (hψ.le_iff_le.mp (le_trans (le_max_left _ _) hn))
    · rw [hxgap n hex]
      exact hN n (le_trans (le_max_right _ _) hn)
  obtain ⟨A, hA, hle⟩ := h.weak_liminf x y hweak
  refine ⟨A, hA, hle.trans ?_⟩
  have hcomp : liminf (fun n ↦ q n (x n)) atTop ≤
      liminf (fun n ↦ q n (x n)) (map ψ atTop) :=
    liminf_le_liminf_of_le hψt
  rw [← liminf_comp] at hcomp
  refine hcomp.trans (le_of_eq ?_)
  congr 1
  funext k
  simp only [Function.comp_apply, hxψ k]

/-- **`lem:mosco-strong-resolvent`** (spacetime–gauge duality manuscript): Mosco convergence
gives strong transported resolvents.  Let the stage graph forms `q_X(u) = ‖A_X u‖²` on
Hilbert spaces `H_X` (weak resolvents `R_X` at a shift `b > 0`) converge in the transported Mosco
sense (`def:transported-mosco`) to the limiting graph form `q_∞(u) = ‖A u‖²` on a Hilbert space
`H_∞` (weak resolvent `R`), all transported into a separable Hilbert carrier `ℋ` by isometries
`J_X`, `J_∞`, with the compatibility `P_X → P_∞` strongly.  Then for every fixed `f ∈ ℋ`,
`J_X R_X J_X^* f → J_∞ R J_∞^* f` strongly.  No compactness is assumed. -/
theorem tendsto_compressedOperator_apply_of_transportedMosco_weak
    [TopologicalSpace.SeparableSpace H]
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
    (hcompat : ∀ g, Tendsto (fun n ↦ J.rangeProjection n g) atTop (𝓝 (Pinf g))) (f : H) :
    Tendsto (fun n ↦ J.compressedOperator Rn n f) atTop
      (𝓝 (transportedLimitOperator Jlim R f)) := by
  classical
  set Jc : Hlim →L[ℂ] H := Jlim.toContinuousLinearMap with hJc
  set g : Hlim := Jc.adjoint f with hg
  set ustar : Hlim := R g with hustar
  set u : ∀ n, Hn n := fun n ↦ Rn n (J.adjointLift n f) with hudef
  have hinnerJ : ∀ (n : ℕ) (x : Hn n),
      inner ℂ x (J.adjointLift n f) = inner ℂ (J.embedding n x) f := by
    intro n x
    exact ContinuousLinearMap.adjoint_inner_right _ x f
  have hinnerLim : ∀ x : Hlim, inner ℂ x g = inner ℂ (Jlim x) f := by
    intro x
    exact ContinuousLinearMap.adjoint_inner_right _ x f
  have hmemu : ∀ n, u n ∈ Dn n := fun n ↦ (hstage n _).mem
  have heul : ∀ n, ‖An n ⟨u n, hmemu n⟩‖ ^ 2 + b * ‖u n‖ ^ 2 =
      (inner ℂ (J.embedding n (u n)) f).re := by
    intro n
    have E := (hstage n (J.adjointLift n f)).weakEuler ⟨u n, hmemu n⟩
    change RCLike.re (inner ℂ (An n ⟨u n, hmemu n⟩) (An n ⟨u n, hmemu n⟩)) +
        b * RCLike.re (inner ℂ (u n) (u n)) =
      RCLike.re (inner ℂ (u n) (J.adjointLift n f)) at E
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq, hinnerJ] at E
    exact E
  -- the energy estimate makes the transported resolvent vectors bounded
  have hbound : ∀ n, ‖u n‖ ≤ 1 / b * ‖f‖ := by
    intro n
    refine ((hstage n (J.adjointLift n f)).norm_le_inv_mul hb).trans ?_
    gcongr
    exact J.norm_adjointLift_apply_le n f
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, -, hφns⟩ := strictMono_subseq_of_tendsto_atTop hns
  -- a weakly convergent subsequence
  obtain ⟨y, φ', hφ', hweak⟩ :=
    (J.reindex (ns ∘ φ)).exists_weaklyConvergent_subsequence_of_bounded
      (fun k ↦ u (ns (φ k))) (1 / b * ‖f‖) (fun k ↦ hbound _)
  -- a further subsequence along which the norms converge
  obtain ⟨ρ, -, φ2, hφ2, hρ⟩ := tendsto_subseq_of_bounded
    (x := fun k ↦ ‖u (ns (φ (φ' k)))‖) (Metric.isBounded_closedBall (x := (0 : ℝ))
      (r := 1 / b * ‖f‖)) (fun k ↦ mem_closedBall_zero_iff.mpr (by rw [norm_norm]; exact hbound _))
  refine ⟨φ ∘ φ' ∘ φ2, ?_⟩
  set ψ : ℕ → ℕ := ns ∘ φ ∘ φ' ∘ φ2 with hψdef
  have hψ : StrictMono ψ := hφns.comp (hφ'.comp hφ2)
  let z : ∀ k, Hn (ψ k) := fun k ↦ u (ψ k)
  have hzweak : ∀ h, Tendsto (fun k ↦ inner ℂ (J.embedding (ψ k) (z k)) h) atTop
      (𝓝 (inner ℂ y h)) := fun h ↦ (hweak h).comp hφ2.tendsto_atTop
  have hznorm : Tendsto (fun k ↦ ‖J.embedding (ψ k) (z k)‖) atTop (𝓝 ρ) := by
    have hfun : (fun k ↦ ‖J.embedding (ψ k) (z k)‖) =
        (fun k ↦ ‖u (ns (φ (φ' k)))‖) ∘ φ2 := by
      funext k; simp only [LinearIsometry.norm_map]; rfl
    rw [hfun]; exact hρ
  suffices hyt : Tendsto (fun k ↦ J.embedding (ψ k) (z k)) atTop
      (𝓝 (transportedLimitOperator Jlim R f)) by
    exact hyt
  have hCz : ∀ k, ‖J.embedding (ψ k) (z k)‖ ≤ 1 / b * ‖f‖ := fun k ↦ by
    rw [LinearIsometry.norm_map]; exact hbound _
  obtain ⟨A0, hA0, hle⟩ :=
    TransportedMoscoConverges.exists_of_strictMono_weak J hmosco Pinf hcompat hψ z _ hCz hzweak
  -- weak lower semicontinuity of the norm
  have hyρ : ‖y‖ ≤ ρ := by
    have h1 : Tendsto (fun k ↦ (inner ℂ (J.embedding (ψ k) (z k)) y).re) atTop
        (𝓝 (‖y‖ ^ 2)) := by
      have := (Complex.continuous_re.tendsto _).comp (hzweak y)
      rwa [show (inner ℂ y y).re = ‖y‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) y] at this
    have h2 : Tendsto (fun k ↦ ‖J.embedding (ψ k) (z k)‖ * ‖y‖) atTop (𝓝 (ρ * ‖y‖)) :=
      hznorm.mul_const _
    have hle' : ‖y‖ ^ 2 ≤ ρ * ‖y‖ :=
      le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun k ↦ by exact re_inner_le_norm (𝕜 := ℂ) _ _)
    have hρ0 : 0 ≤ ρ := ge_of_tendsto' hznorm fun _ ↦ norm_nonneg _
    rcases (norm_nonneg y).eq_or_lt with h0 | hpos
    · rw [← h0]; exact hρ0
    · nlinarith
  -- the energies along the subsequence
  set e : ℝ := (inner ℂ y f).re with hedef
  have he : Tendsto (fun k ↦ (inner ℂ (J.embedding (ψ k) (z k)) f).re) atTop (𝓝 e) :=
    (Complex.continuous_re.tendsto _).comp (hzweak f)
  set c : ℝ := e - b * ρ ^ 2 with hcdef
  have hqk : Tendsto (fun k ↦ ‖An (ψ k) ⟨z k, hmemu (ψ k)⟩‖ ^ 2) atTop (𝓝 c) := by
    have hfun : (fun k ↦ ‖An (ψ k) ⟨z k, hmemu (ψ k)⟩‖ ^ 2) = fun k ↦
        (inner ℂ (J.embedding (ψ k) (z k)) f).re - b * ‖J.embedding (ψ k) (z k)‖ ^ 2 := by
      funext k; rw [LinearIsometry.norm_map, ← heul (ψ k)]; ring
    rw [hfun]
    exact he.sub ((hznorm.pow 2).const_mul b)
  have hc0 : 0 ≤ c := ge_of_tendsto' hqk (fun k ↦ sq_nonneg _)
  have hliminf : liminf (fun k ↦ ennrealOperatorGraphEnergy (Dn (ψ k)) (An (ψ k)) (z k)) atTop =
      ENNReal.ofReal c := by
    have hfun : (fun k ↦ ennrealOperatorGraphEnergy (Dn (ψ k)) (An (ψ k)) (z k)) =
        fun k ↦ ENNReal.ofReal (‖An (ψ k) ⟨z k, hmemu (ψ k)⟩‖ ^ 2) := by
      funext k; exact ennrealOperatorGraphEnergy_of_mem _ _ (hmemu (ψ k))
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
  -- recovery sequence for the limit minimiser and stage minimality
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
  have hObju : ∀ k, (ennrealOperatorGraphEnergy (Dn (ψ k)) (An (ψ k)) (z k)).toReal +
      b * ‖z k‖ ^ 2 - 2 * (inner ℂ (J.embedding (ψ k) (z k)) f).re =
        -(inner ℂ (J.embedding (ψ k) (z k)) f).re := by
    intro k
    rw [ennrealOperatorGraphEnergy_of_mem _ _ (hmemu (ψ k)), ENNReal.toReal_ofReal (sq_nonneg _)]
    linarith [heul (ψ k)]
  have hminimal : ∀ᶠ k in atTop,
      -(inner ℂ (J.embedding (ψ k) (z k)) f).re ≤
        (ennrealOperatorGraphEnergy (Dn (ψ k)) (An (ψ k)) (wseq (ψ k))).toReal +
          b * ‖wseq (ψ k)‖ ^ 2 - 2 * (inner ℂ (J.embedding (ψ k) (wseq (ψ k))) f).re := by
    filter_upwards [hψ.tendsto_atTop.eventually hwfin] with k hk
    have hwD : wseq (ψ k) ∈ Dn (ψ k) :=
      (ennrealOperatorGraphEnergy_ne_top_iff _ _ _).mp hk
    have hmin := operatorGraph_resolventObjective_minimizer (Dn (ψ k)) (An (ψ k)) b hb.le
      (J.adjointLift (ψ k) f) (z k) (hstage (ψ k) _) (wseq (ψ k)) hwD
    simp only [resolventObjective] at hmin
    change _ + _ - 2 * RCLike.re (inner ℂ (z k) (J.adjointLift (ψ k) f)) ≤
      _ + _ - 2 * RCLike.re (inner ℂ (wseq (ψ k)) (J.adjointLift (ψ k) f)) at hmin
    rw [hinnerJ, hinnerJ] at hmin
    rw [← hObju k]
    exact hmin
  have hlimu : Tendsto (fun k ↦ -(inner ℂ (J.embedding (ψ k) (z k)) f).re) atTop (𝓝 (-e)) :=
    he.neg
  have hle2 : -e ≤ Lstar :=
    le_of_tendsto_of_tendsto hlimu (hObjw.comp hψ.tendsto_atTop) hminimal
  -- compare the limit objectives (strict convexity)
  have hgap := operatorGraph_resolventObjective_sub_eq D A b g ustar (hlimit g) A0 hA0D
  simp only [resolventObjective] at hgap
  change _ + _ - 2 * RCLike.re (inner ℂ A0 g) - (_ + _ - 2 * RCLike.re (inner ℂ ustar g)) = _
    at hgap
  rw [ennrealOperatorGraphEnergy_of_mem D A hA0D, ennrealOperatorGraphEnergy_of_mem D A hustarD,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _),
    hinnerLim, hinnerLim, hA0] at hgap
  have hnormA0 : ‖A0‖ = ‖y‖ := by rw [← hA0, LinearIsometry.norm_map]
  rw [hnormA0] at hgap
  change _ = _ at hgap
  simp only [RCLike.re_to_complex] at hgap
  have hyρsq : ‖y‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyρ 2
  have hbyρ : b * ‖y‖ ^ 2 ≤ b * ρ ^ 2 := mul_le_mul_of_nonneg_left hyρsq hb.le
  have hsq : b * ‖A0 - ustar‖ ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ‖A ⟨A0, hA0D⟩ - A ⟨ustar, hustarD⟩‖]
  have hzero : ‖A0 - ustar‖ ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right hsq hb) (sq_nonneg _)
  have hA0eq : A0 = ustar :=
    sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hzero))
  -- the norms converge to the norm of the weak limit
  have hρy2 : ρ ^ 2 ≤ ‖y‖ ^ 2 := by
    have hb' : b * ρ ^ 2 ≤ b * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg ‖A ⟨A0, hA0D⟩ - A ⟨ustar, hustarD⟩‖, sq_nonneg ‖A0 - ustar‖]
    exact le_of_mul_le_mul_left hb' hb
  have hρeq : ρ ^ 2 = ‖y‖ ^ 2 := le_antisymm hρy2 hyρsq
  -- weak convergence plus norm convergence gives strong convergence
  have hstrong : Tendsto (fun k ↦ J.embedding (ψ k) (z k)) atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsqT : Tendsto (fun k ↦ ‖J.embedding (ψ k) (z k) - y‖ ^ 2) atTop (𝓝 0) := by
      have hfun : (fun k ↦ ‖J.embedding (ψ k) (z k) - y‖ ^ 2) = fun k ↦
          ‖J.embedding (ψ k) (z k)‖ ^ 2 - 2 * (inner ℂ (J.embedding (ψ k) (z k)) y).re +
            ‖y‖ ^ 2 := by
        funext k
        rw [@norm_sub_sq ℂ]
        rfl
      rw [hfun]
      have h1 : Tendsto (fun k ↦ (inner ℂ (J.embedding (ψ k) (z k)) y).re) atTop
          (𝓝 (‖y‖ ^ 2)) := by
        have := (Complex.continuous_re.tendsto _).comp (hzweak y)
        rwa [show (inner ℂ y y).re = ‖y‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) y] at this
      have h2 := ((hznorm.pow 2).sub (h1.const_mul 2)).add_const (‖y‖ ^ 2)
      convert h2 using 2
      rw [hρeq]; ring
    have hsqrt := hsqT.sqrt
    simp only [Real.sqrt_zero] at hsqrt
    refine hsqrt.congr fun k ↦ ?_
    exact Real.sqrt_sq (norm_nonneg _)
  rw [transportedLimitOperator_apply, ← hA0, hA0eq] at *
  exact hstrong

/-- Non-vacuity of `tendsto_compressedOperator_apply_of_transportedMosco_weak`: the hypotheses
hold for the witness of `CompactMoscoGeneralWitness` (common carrier `ℂ²`, limiting space `ℂ`
embedded as the **proper** line `ℂ e₀`, stage and limit forms `‖u‖²`), with `P_∞ = J_∞ J_∞^*`. -/
theorem transportedMoscoWeak_nonvacuous (f : CompactMoscoGeneralWitness.Hw) :
    Tendsto (fun n ↦ CompactMoscoGeneralWitness.Jw.compressedOperator
        (fun _ ↦ CompactMoscoGeneralWitness.Rw) n f) atTop
      (𝓝 (transportedLimitOperator CompactMoscoGeneralWitness.Jlimw
        CompactMoscoGeneralWitness.Rw f)) :=
  tendsto_compressedOperator_apply_of_transportedMosco_weak CompactMoscoGeneralWitness.Jw
    CompactMoscoGeneralWitness.Jlimw (fun _ ↦ ⊤)
    (fun _ ↦ boundedOperatorGraphMap CompactMoscoGeneralWitness.Aw) ⊤
    (boundedOperatorGraphMap CompactMoscoGeneralWitness.Aw) 1 one_pos
    (fun _ ↦ CompactMoscoGeneralWitness.Rw) CompactMoscoGeneralWitness.Rw
    CompactMoscoGeneralWitness.hstage (CompactMoscoGeneralWitness.hstage 0)
    CompactMoscoGeneralWitness.hmosco _ CompactMoscoGeneralWitness.hcompat f

end RenewalGeometry.VaryingHilbert.System
