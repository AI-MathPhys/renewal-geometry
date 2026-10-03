/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.AsymptoticCollectiveCompactness
import RenewalGeometry.OperatorLimits.TransportedMoscoStrongResolventConvergence
import RenewalGeometry.OperatorLimits.OperatorGraphResolventBound

/-!
# Asymptotic form compactness of a cofinal family of cutoffs

`def:asymptotic-compactness` of the spacetime–gauge duality manuscript is a property of a
**cofinal family** of cutoffs: every sequence `A_X ∈ D(q_X)` of bounded energy has a subsequence
whose transported vectors converge.  When the cutoffs are enumerated by `ℕ`, a sequence of
cutoffs going to infinity is a strictly increasing reindexing, so the enumeration-independent
rendering of the definition is the named predicate `System.AsymptoticallyCompact` (the literal
`ℕ`-indexed encoding of `TransportedMoscoAsymptoticCompactness.lean`) imposed on **every cofinal
subfamily** of cutoffs.  This is the form used in the manuscript's proofs of
`lem:collective-compactness` and `lem:collective-norm`, which pass to "a cofinal sequence of
indices".

* `System.CofinallyAsymptoticallyCompact J q`: `(J.reindex φ).AsymptoticallyCompact (q ∘ φ)` for
  every strictly increasing `φ`; `CofinallyAsymptoticallyCompactFamily` adds the limit clause
  `LimitFormCompact`.  `CofinallyAsymptoticallyCompact.asymptoticallyCompact` recovers the
  literal predicate (`φ = id`).
* `OperatorGraphResolventEquation.norm_sq_graph_le`: the energy bound
  `‖A u‖² ≤ b⁻¹‖g‖²` for a weak graph resolvent at shift `b > 0` (`eq:resolvent-energy-bound`).
* `collectivelyCompact_of_cofinallyAsymptoticallyCompact`: for finite-dimensional cutoff spaces,
  cofinal asymptotic form compactness gives compact-container collective compactness of the
  stage graph resolvents (`lem:collective-compactness`).
-/

open Filter Topology
open scoped ENNReal

noncomputable section

namespace RenewalGeometry.VaryingHilbert

universe u v w w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {Hlim : Type w'} [NormedAddCommGroup Hlim] [InnerProductSpace K Hlim]

namespace System

/-- **`def:asymptotic-compactness`, stage clause, for a cofinal family of cutoffs**: every
cofinal subfamily `X_k = φ k` (`φ` strictly increasing) is asymptotically compact in the sense of
`System.AsymptoticallyCompact`. -/
def CofinallyAsymptoticallyCompact (J : System (K := K) (H := H) (Hn := Hn))
    (q : (n : ℕ) → Hn n → ℝ≥0∞) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    (J.reindex φ).AsymptoticallyCompact (Hn := fun k ↦ Hn (φ k)) (fun k ↦ q (φ k))

/-- The cofinal form contains the literal `ℕ`-indexed predicate. -/
theorem CofinallyAsymptoticallyCompact.asymptoticallyCompact
    {J : System (K := K) (H := H) (Hn := Hn)} {q : (n : ℕ) → Hn n → ℝ≥0∞}
    (h : J.CofinallyAsymptoticallyCompact q) : J.AsymptoticallyCompact q :=
  h id strictMono_id

end System

/-- **`def:asymptotic-compactness`** for a cofinal family of cutoffs: the stage clause on every
cofinal subfamily together with the limit clause `LimitFormCompact`. -/
def CofinallyAsymptoticallyCompactFamily (J : System (K := K) (H := H) (Hn := Hn))
    (Jlim : Hlim →ₗᵢ[K] H) (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : Hlim → ℝ≥0∞) : Prop :=
  J.CofinallyAsymptoticallyCompact q ∧ LimitFormCompact Jlim qlim

/-- Every cofinal subfamily of a cofinally asymptotically compact family is asymptotically
compact in the literal sense, together with the limit clause. -/
theorem CofinallyAsymptoticallyCompactFamily.reindex
    {J : System (K := K) (H := H) (Hn := Hn)} {Jlim : Hlim →ₗᵢ[K] H}
    {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : Hlim → ℝ≥0∞}
    (h : CofinallyAsymptoticallyCompactFamily J Jlim q qlim) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    AsymptoticallyCompactFamily (J.reindex φ) Jlim (fun k ↦ q (φ k)) qlim :=
  ⟨h.1 φ hφ, h.2⟩

/-- The resolvent energy bound for a weak graph resolvent at a positive shift:
`‖A u‖² ≤ b⁻¹ ‖g‖²` (and `‖u‖ ≤ b⁻¹ ‖g‖`). -/
theorem OperatorGraphResolventEquation.norm_sq_graph_le
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup G] [InnerProductSpace K G]
    {D : Submodule K E} {A : D →ₗ[K] G} {b : ℝ} {g x : E}
    (h : OperatorGraphResolventEquation D A b g x) (hb : 0 < b) :
    ‖A ⟨x, h.mem⟩‖ ^ 2 ≤ 1 / b * ‖g‖ ^ 2 := by
  have hx := h.norm_le_inv_mul hb
  have heuler := h.weakEuler ⟨x, h.mem⟩
  rw [← norm_sq_eq_re_inner (𝕜 := K) (A ⟨x, h.mem⟩)] at heuler
  have hre : RCLike.re (inner K x g) ≤ ‖x‖ * ‖g‖ := re_inner_le_norm _ _
  have hxx : 0 ≤ b * RCLike.re (inner K (⟨x, h.mem⟩ : D).1 x) := by
    change 0 ≤ b * RCLike.re (inner K x x)
    rw [← norm_sq_eq_re_inner (𝕜 := K) x]
    positivity
  have hxg : ‖x‖ * ‖g‖ ≤ 1 / b * ‖g‖ * ‖g‖ := by
    gcongr
  change ‖A ⟨x, h.mem⟩‖ ^ 2 + b * RCLike.re (inner K x x) = RCLike.re (inner K x g) at heuler
  change 0 ≤ b * RCLike.re (inner K x x) at hxx
  nlinarith

/-- On a finite-dimensional (proper) common carrier every family is asymptotically compact: a
bounded-energy sequence has bounded transported vectors. -/
theorem System.asymptoticallyCompact_of_properSpace [ProperSpace H]
    (J : System (K := K) (H := H) (Hn := Hn)) (q : (n : ℕ) → Hn n → ℝ≥0∞) :
    J.AsymptoticallyCompact q := by
  rintro x ⟨C, hC, hbound⟩
  have hx : ∀ n, J.embedding n (x n) ∈ Metric.closedBall (0 : H) (Real.sqrt C.toReal) := by
    intro n
    rw [mem_closedBall_zero_iff, LinearIsometry.norm_map]
    apply Real.le_sqrt_of_sq_le
    rw [← ENNReal.ofReal_le_iff_le_toReal hC]
    exact le_trans le_self_add (hbound n)
  obtain ⟨y, -, φ, hφ, hy⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hx
  exact ⟨φ, hφ, y, hy⟩

/-- On a finite-dimensional common carrier every family is cofinally asymptotically compact,
together with the limit clause. -/
theorem cofinallyAsymptoticallyCompactFamily_of_properSpace [ProperSpace H]
    (J : System (K := K) (H := H) (Hn := Hn)) (Jlim : Hlim →ₗᵢ[K] H)
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : Hlim → ℝ≥0∞) :
    CofinallyAsymptoticallyCompactFamily J Jlim q qlim :=
  ⟨fun φ _ ↦ (J.reindex φ).asymptoticallyCompact_of_properSpace _,
    (constantEmbeddingSystem Jlim).asymptoticallyCompact_of_properSpace _⟩

variable [CompleteSpace H] [∀ n, CompleteSpace (Hn n)]

/-- **Collective compactness from cofinal asymptotic form compactness**
(`lem:collective-compactness`).  For finite-dimensional cutoff spaces and stage graph forms
`q_X(u) = ‖A_X u‖²` with weak resolvents `R_X` at a shift `b > 0`, if the family is
asymptotically compact along every cofinal subfamily of cutoffs, then the stage resolvents are
collectively compact: all embedded unit-ball images `J_X R_X (B_1)` lie in one compact set. -/
theorem collectivelyCompact_of_cofinallyAsymptoticallyCompact
    [∀ n, FiniteDimensional K (Hn n)]
    {Fn : ℕ → Type*} [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
    (J : System (K := K) (H := H) (Hn := Hn))
    (Dn : ∀ n, Submodule K (Hn n)) (An : ∀ n, Dn n →ₗ[K] Fn n)
    (b : ℝ) (hb : 0 < b) (Rn : ∀ n, Hn n →L[K] Hn n)
    (hstage : ∀ n g, OperatorGraphResolventEquation (Dn n) (An n) b g (Rn n g))
    (hac : J.CofinallyAsymptoticallyCompact (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))) :
    J.CollectivelyCompact Rn := by
  classical
  let Tn : ∀ n, H →L[K] Hn n := fun n ↦ (Rn n).comp (J.adjointLift n)
  have hcc : J.CollectivelyCompact (Hn := fun _ ↦ H) Tn := by
    apply collectivelyCompact_of_seq_of_stage_compact J Tn
    · intro φ hφ x hx
      let v : ∀ k, Hn (φ k) := fun k ↦ Tn (φ k) (x k)
      have hmem : ∀ k, v k ∈ Dn (φ k) := fun k ↦ (hstage (φ k) _).mem
      have hgk : ∀ k, ‖J.adjointLift (φ k) (x k)‖ ≤ 1 := fun k ↦ by
        let e : Hn (φ k) →L[K] H := (J.embedding (φ k)).toContinuousLinearMap
        calc ‖J.adjointLift (φ k) (x k)‖ = ‖e.adjoint (x k)‖ := rfl
          _ ≤ ‖e.adjoint‖ * ‖x k‖ := (e.adjoint).le_opNorm _
          _ = ‖e‖ * ‖x k‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
          _ ≤ 1 * 1 := by
            gcongr
            · exact (J.embedding (φ k)).norm_toContinuousLinearMap_le
            · exact hx k
          _ = 1 := one_mul _
      have hbound : ∀ k, ENNReal.ofReal (‖v k‖ ^ 2) +
          ennrealOperatorGraphEnergy (Dn (φ k)) (An (φ k)) (v k) ≤
            ENNReal.ofReal (1 / b * (1 / b) + 1 / b) := by
        intro k
        have E := hstage (φ k) (J.adjointLift (φ k) (x k))
        have h1 := E.norm_le_inv_mul hb
        have h2 := E.norm_sq_graph_le hb
        have hg := hgk k
        rw [ennrealOperatorGraphEnergy, dif_pos (hmem k), ← ENNReal.ofReal_add (sq_nonneg _)
          (sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have hb1 : 0 < 1 / b := by positivity
        have hv : ‖v k‖ ≤ 1 / b := by
          calc ‖v k‖ ≤ 1 / b * ‖J.adjointLift (φ k) (x k)‖ := h1
            _ ≤ 1 / b * 1 := by gcongr
            _ = 1 / b := mul_one _
        have hA : ‖An (φ k) ⟨v k, hmem k⟩‖ ^ 2 ≤ 1 / b := by
          calc ‖An (φ k) ⟨v k, hmem k⟩‖ ^ 2 ≤ 1 / b * ‖J.adjointLift (φ k) (x k)‖ ^ 2 := h2
            _ ≤ 1 / b * 1 := by
                gcongr
                calc ‖J.adjointLift (φ k) (x k)‖ ^ 2 ≤ 1 ^ 2 := by gcongr
                  _ = 1 := one_pow 2
            _ = 1 / b := mul_one _
        have hv2 : ‖v k‖ ^ 2 ≤ 1 / b * (1 / b) := by
          rw [sq]; exact mul_le_mul hv hv (norm_nonneg _) hb1.le
        linarith
      obtain ⟨ψ, hψ, y, hy⟩ := hac φ hφ v
        ⟨ENNReal.ofReal (1 / b * (1 / b) + 1 / b), ENNReal.ofReal_ne_top, hbound⟩
      exact ⟨ψ, hψ, y, hy⟩
    · intro n
      exact J.compressedOperator_isCompactOperator_of_finiteDimensional Rn n
  obtain ⟨C, hC, hsub⟩ := hcc
  refine ⟨C, hC, fun n ↦ ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply hsub n
  refine ⟨J.embedding n x, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, LinearIsometry.norm_map]
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  · change J.embedding n (Rn n (J.adjointLift n (J.embedding n x))) = J.embedding n (Rn n x)
    rw [System.adjointLift_embedding]

/-! ### The literal `ℕ`-indexed predicate is strictly weaker -/

namespace CofinalAsymptoticCompactnessSeparation

/-- The orthonormal vectors `e_n` of `ℓ²(ℕ)`. -/
def sepVec (n : ℕ) : lp (fun _ : ℕ ↦ ℂ) 2 := lp.single 2 n (1 : ℂ)

theorem sepVec_norm (n : ℕ) : ‖sepVec n‖ = 1 := by
  rw [sepVec, lp.norm_single (by norm_num)]; simp

theorem sepVec_dist {i j : ℕ} (hij : i ≠ j) : ‖sepVec i - sepVec j‖ ^ 2 = 2 := by
  classical
  rw [@norm_sub_sq ℂ, sepVec_norm, sepVec_norm]
  have h0 : inner ℂ (sepVec i) (sepVec j) = 0 := by
    rw [sepVec, lp.inner_single_left, sepVec, lp.single_apply, Pi.single_eq_of_ne hij]
    simp
  rw [h0]; simp; norm_num

/-- Stage `n` is the line `ℂ e_n` of `ℓ²(ℕ)`. -/
def sepSystem : System (K := ℂ) (H := lp (fun _ : ℕ ↦ ℂ) 2) (Hn := fun _ : ℕ ↦ ℂ) :=
  ⟨fun n ↦ LinearIsometry.toSpanSingleton ℂ _ (sepVec_norm n)⟩

/-- The form is `0` at even cutoffs and has domain `{0}` at odd cutoffs. -/
def sepForm (n : ℕ) (z : ℂ) : ℝ≥0∞ := if Even n then 0 else if z = 0 then 0 else ∞

/-- **Separation example.**  The literal `ℕ`-indexed predicate `System.AsymptoticallyCompact`
does not imply its cofinal form: here every bounded-energy sequence vanishes at odd cutoffs (so
the odd subsequence converges), but along the even cutoffs the unit vectors `e_{2k}` have no
convergent subsequence.  Hence the paper's proof of `lem:collective-norm`, which passes to a
cofinal sequence of cutoffs, needs the cofinal reading of `def:asymptotic-compactness`. -/
theorem asymptoticallyCompact_not_cofinal :
    sepSystem.AsymptoticallyCompact sepForm ∧ ¬ sepSystem.CofinallyAsymptoticallyCompact sepForm := by
  constructor
  · rintro x ⟨C, hC, hbound⟩
    have hodd : ∀ k, x (2 * k + 1) = 0 := by
      intro k
      by_contra hne
      have h := hbound (2 * k + 1)
      have hodd : ¬ Even (2 * k + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one k
      simp only [sepForm, hodd, if_false, hne] at h
      exact hC (top_le_iff.mp (le_trans le_add_self h))
    refine ⟨fun k ↦ 2 * k + 1, fun a b hab ↦ by simp only; omega, 0, ?_⟩
    have : (fun k ↦ sepSystem.embedding (2 * k + 1) (x (2 * k + 1))) = fun _ ↦ 0 := by
      funext k; rw [hodd k, map_zero]
    rw [this]; exact tendsto_const_nhds
  · intro hcof
    obtain ⟨ψ, hψ, y, hy⟩ := hcof (fun k ↦ 2 * k) (fun a b hab ↦ by simp only; omega) (fun _ ↦ (1 : ℂ))
      ⟨1, ENNReal.one_ne_top, fun k ↦ by simp [sepForm]⟩
    have hcs := hy.cauchySeq
    rw [Metric.cauchySeq_iff'] at hcs
    obtain ⟨N, hN⟩ := hcs 1 one_pos
    have h := hN (N + 1) (Nat.le_succ N)
    simp only [System.reindex_embedding, sepSystem, LinearIsometry.toSpanSingleton_apply,
      one_smul, dist_eq_norm] at h
    have hne : 2 * ψ (N + 1) ≠ 2 * ψ N := by
      have : ψ N < ψ (N + 1) := hψ (Nat.lt_succ_self N)
      omega
    have h2 := sepVec_dist hne
    nlinarith [norm_nonneg (sepVec (2 * ψ (N + 1)) - sepVec (2 * ψ N))]

end CofinalAsymptoticCompactnessSeparation

end RenewalGeometry.VaryingHilbert
