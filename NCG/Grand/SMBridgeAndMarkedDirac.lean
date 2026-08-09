/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMBridgeTransparent
import NCG.Grand.CrossSupportGenerator
import NCG.Grand.GrandGenerationLaplacian
import NCG.Grand.SMGroup
import NCG.Grand.SMMarkedDirac
import NCG.Grand.OccurrenceChoiSource
import NCG.Grand.GrandScoreBus
import NCG.Grand.GrandScoreCross
import NCG.Flagship.ADMAudit
import NCG.Flagship.CrossTomography

/-!
# Standard-Model bridge transparency and marked Dirac projection

Completes the remaining manuscript clauses of ten EASY-tier
records on top of their existing partial layers:

* `thm:SM-bridge-transparent` — adjoint-direction commutant
  cancellation and the all-edges/both-directions equivalence
  (`sm_bridge_transparent_adjoint`,
  `sm_bridge_transparent_edges`, `sm_bridge_transparent_exact`);
* `thm:SM-cross-support-generator` — the boxed operational
  small-time limit `t⁻¹ P_L e^{t𝓛}(P_R X P_R) P_L → Φ_{L←R}(X)`
  (`cross_support_generator_operational`);
* `thm:SM-generation-Laplacian` — the quantitative rigidity
  margin `‖X - P_{{A,B}'}X‖² ≤ λ⁻¹(‖[A,X]‖² + ‖[B,X]‖²)`
  (`sm_generation_laplacian_margin`);
* `thm:SM-group` — first-isomorphism packaging of the boxed
  quotient `S(U(3)×U(2)) ≅ (SU(3)×SU(2)×U(1))/ℤ₆`
  (`smGroupDetLocus`, `smGroupPhi`, `smGroupPhi_surjective`,
  `smGroupPhi_ker_iff`, `smGroupQuotientIso`, `sm_group_exact`);
* `thm:SM-marked-Dirac` — reconstruction from the literal
  `Δ_null^D = 0` hypothesis (`sm_marked_dirac_hankel_projection`,
  `sm_marked_dirac_null_exact`);
* `thm:SM-occurrence-Choi-source` — minimal-support clause
  `supp Γ_occ = supp J_occ` and the record bundle
  (`occurrence_choi_minimal_support`,
  `occurrence_choi_source_exact`);
* `thm:SM-score-bus` — Kraus resolution, complete positivity,
  HS self-adjointness, phase/deck covariance, fixed algebra,
  spectral gap `1/2`, branch probabilities `1/4`
  (`sm_score_bus_kraus` … `sm_score_bus_exact`);
* `thm:SM-score-cross` — assembly of the boxed cross maps from
  the score-bus channel, absorbed effects, and the Kossakowski
  data (`sm_score_cross_assembled_forward`,
  `sm_score_cross_assembled_reverse`, `sm_score_cross_effects`,
  `sm_score_cross_kossakowski`);
* `thm:SMST-Einstein-residual-quotient` — exact sequence,
  unique induced propagator, and the boxed three-way feed
  alternative (`einstein_residual_quotient_sequence`,
  `einstein_residual_feed_alternative`,
  `einstein_residual_zero_branch`);
* `thm:SMST-clock-geometry-audit` — Gram-rank increment,
  principal-cosine contraction normal form, and the
  polarization reconstruction of the cross Gram
  (`clock_geometry_rank_increment`,
  `clock_geometry_contraction_normal_form`,
  `clock_geometry_cross_polarization`).
-/

open Matrix
open scoped Kronecker

namespace NCG

/-! ## `thm:SM-bridge-transparent`: all edges, both directions -/

/-- Commutant cancellation across a Kronecker edge: for a
nonzero carrier factor `D`, the intertwining relation
`(1 ⊗ R')·(D ⊗ F) = (D ⊗ F)·(1 ⊗ R)` holds exactly when the
residue factors intertwine, `R'F = FR`. -/
theorem sm_bridge_kron_cancel {v w a : Type*} [Fintype v]
    [Fintype w] [Fintype a] [DecidableEq v] [DecidableEq w]
    (D : Matrix v w ℂ) (F R R' : Matrix a a ℂ)
    (hD : ∃ i j, D i j ≠ 0) :
    ((1 : Matrix v v ℂ) ⊗ₖ R') * (D ⊗ₖ F)
        = (D ⊗ₖ F) * ((1 : Matrix w w ℂ) ⊗ₖ R)
      ↔ R' * F = F * R := by
  constructor
  · intro hcomm
    obtain ⟨i, j, hij⟩ := hD
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one] at hcomm
    ext x y
    have h := congrArg (fun M => M (i, x) (j, y)) hcomm
    simp only [Matrix.kroneckerMap_apply] at h
    exact mul_left_cancel₀ hij h
  · intro hcomm
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, hcomm]

/-- `thm:SM-bridge-transparent`, adjoint direction: the
commutant element intertwines through `Y_e^* = D^* ⊗ F^*`
exactly when `R F^* = F^* R'` — the manuscript's second residue
equation. -/
theorem sm_bridge_transparent_adjoint {v w a : Type*}
    [Fintype v] [Fintype w] [Fintype a] [DecidableEq v]
    [DecidableEq w]
    (D : Matrix v w ℂ) (F R R' : Matrix a a ℂ)
    (hD : ∃ i j, D i j ≠ 0) :
    ((1 : Matrix w w ℂ) ⊗ₖ R) * (D ⊗ₖ F)ᴴ
        = (D ⊗ₖ F)ᴴ * ((1 : Matrix v v ℂ) ⊗ₖ R')
      ↔ R * Fᴴ = Fᴴ * R' := by
  obtain ⟨i, j, hij⟩ := hD
  rw [Matrix.conjTranspose_kronecker]
  exact sm_bridge_kron_cancel Dᴴ Fᴴ R' R
    ⟨j, i, by simpa [Matrix.conjTranspose_apply] using
      star_ne_zero.mpr hij⟩

/-- `thm:SM-bridge-transparent`, all edges and both directions:
an internal-carrier commutant element `1 ⊗ R'` (target) /
`1 ⊗ R` (source) commutes with **every** edge coefficient
`Y_e = D_e ⊗ F_e` **and** every adjoint `Y_e^*` exactly when
for each edge the two residue equations
`R'F_e = F_eR` and `RF_e^* = F_e^*R'` hold. -/
theorem sm_bridge_transparent_edges {v w a ι : Type*}
    [Fintype v] [Fintype w] [Fintype a] [DecidableEq v]
    [DecidableEq w]
    (D : ι → Matrix v w ℂ) (F : ι → Matrix a a ℂ)
    (R R' : Matrix a a ℂ) (hD : ∀ e, ∃ i j, D e i j ≠ 0) :
    (∀ e, ((1 : Matrix v v ℂ) ⊗ₖ R') * (D e ⊗ₖ F e)
          = (D e ⊗ₖ F e) * ((1 : Matrix w w ℂ) ⊗ₖ R)
        ∧ ((1 : Matrix w w ℂ) ⊗ₖ R) * (D e ⊗ₖ F e)ᴴ
          = (D e ⊗ₖ F e)ᴴ * ((1 : Matrix v v ℂ) ⊗ₖ R'))
      ↔ (∀ e, R' * F e = F e * R
          ∧ R * (F e)ᴴ = (F e)ᴴ * R') :=
  forall_congr' fun e =>
    and_congr (sm_bridge_kron_cancel (D e) (F e) R R' (hD e))
      (sm_bridge_transparent_adjoint (D e) (F e) R R' (hD e))

/-- `thm:SM-bridge-transparent`, exact bundle: for every edge
the two boxed square identities
`Y_e^*Y_e = c_e(p_e ⊗ P_e²)`, `Y_eY_e^* = c_e(q_e ⊗ U_eP_e²U_e^*)`
hold, and the commutant cancellation holds across all edges in
both directions — so the generation/flavour commutant is
independent of every nonzero carrier factor. -/
theorem sm_bridge_transparent_exact {v w a ι : Type*}
    [Fintype v] [Fintype w] [Fintype a] [DecidableEq v]
    [DecidableEq w] [DecidableEq a]
    (D : ι → Matrix v w ℂ) (U P : ι → Matrix a a ℂ)
    (c : ι → ℂ) (p : ι → Matrix w w ℂ) (q : ι → Matrix v v ℂ)
    (hDl : ∀ e, (D e)ᴴ * D e = c e • p e)
    (hDr : ∀ e, D e * (D e)ᴴ = c e • q e)
    (hU : ∀ e, (U e)ᴴ * U e = 1) (hP : ∀ e, (P e)ᴴ = P e)
    (hD : ∀ e, ∃ i j, D e i j ≠ 0) :
    (∀ e, (D e ⊗ₖ (U e * P e))ᴴ * (D e ⊗ₖ (U e * P e))
        = c e • (p e ⊗ₖ (P e * P e)))
    ∧ (∀ e, (D e ⊗ₖ (U e * P e)) * (D e ⊗ₖ (U e * P e))ᴴ
        = c e • (q e ⊗ₖ (U e * (P e * P e) * (U e)ᴴ)))
    ∧ (∀ R R' : Matrix a a ℂ,
        (∀ e, ((1 : Matrix v v ℂ) ⊗ₖ R')
              * (D e ⊗ₖ (U e * P e))
            = (D e ⊗ₖ (U e * P e))
              * ((1 : Matrix w w ℂ) ⊗ₖ R)
          ∧ ((1 : Matrix w w ℂ) ⊗ₖ R)
              * (D e ⊗ₖ (U e * P e))ᴴ
            = (D e ⊗ₖ (U e * P e))ᴴ
              * ((1 : Matrix v v ℂ) ⊗ₖ R'))
        ↔ (∀ e, R' * (U e * P e) = (U e * P e) * R
            ∧ R * (U e * P e)ᴴ = (U e * P e)ᴴ * R')) :=
  ⟨fun e => (sm_bridge_transparent (D e) (U e) (P e) (c e)
      (p e) (q e) (hDl e) (hDr e) (hU e) (hP e)).1,
    fun e => (sm_bridge_transparent (D e) (U e) (P e) (c e)
      (p e) (q e) (hDl e) (hDr e) (hU e) (hP e)).2.1,
    fun R R' => sm_bridge_transparent_edges D
      (fun e => U e * P e) R R' hD⟩

/-! ## `thm:SM-marked-Dirac`: literal `Δ_null^D = 0` input -/

/-- The row-space projection used in the marked-Dirac null test
is the manuscript's `P_ℍ = ℍ_d ℍ_d^†`: for a full-row-rank Gram
factor `R` of `ℍ = R^*R`, the Moore–Penrose product
`ℍ · (R^*(RR^*)⁻²R)` collapses to `R^*(RR^*)⁻¹R`. -/
theorem sm_marked_dirac_hankel_projection {r w : Type*}
    [Fintype r] [Fintype w] [DecidableEq r]
    (R : Matrix r w ℂ) [Invertible (R * Rᴴ)] :
    (Rᴴ * R) * (Rᴴ * ((R * Rᴴ)⁻¹ * (R * Rᴴ)⁻¹) * R)
      = Rᴴ * (R * Rᴴ)⁻¹ * R := by
  calc (Rᴴ * R) * (Rᴴ * ((R * Rᴴ)⁻¹ * (R * Rᴴ)⁻¹) * R)
      = Rᴴ * ((R * Rᴴ) * (R * Rᴴ)⁻¹) * ((R * Rᴴ)⁻¹ * R) := by
        simp only [Matrix.mul_assoc]
    _ = Rᴴ * (R * Rᴴ)⁻¹ * R := by
        rw [Matrix.mul_inv_of_invertible, Matrix.mul_one,
          Matrix.mul_assoc]

open scoped ComplexOrder in
/-- `thm:SM-marked-Dirac` with the literal null hypothesis: if
the manuscript's null test
`Δ_null^D = ‖(I-P_ℍ)𝕹‖² + ‖𝕹(I-P_ℍ)‖² = 0` holds (HS norms
rendered as traces of Gram squares), then the boxed
reconstruction `D_R = (R^†)^* 𝕹 R^†` satisfies `𝕹 = R^*D_RR`
exactly, and it is the unique such packet operator. -/
theorem sm_marked_dirac_null_exact {r w : Type*} [Fintype r]
    [Fintype w] [DecidableEq r] [DecidableEq w]
    (R : Matrix r w ℂ) [Invertible (R * Rᴴ)]
    (N : Matrix w w ℂ)
    (hnull :
      ((((1 : Matrix w w ℂ) - Rᴴ * (R * Rᴴ)⁻¹ * R) * N)ᴴ
          * (((1 : Matrix w w ℂ) - Rᴴ * (R * Rᴴ)⁻¹ * R) * N)).trace
        + ((N * ((1 : Matrix w w ℂ) - Rᴴ * (R * Rᴴ)⁻¹ * R))ᴴ
          * (N * ((1 : Matrix w w ℂ)
              - Rᴴ * (R * Rᴴ)⁻¹ * R))).trace = 0) :
    (N = Rᴴ * ((Rᴴ * (R * Rᴴ)⁻¹)ᴴ * N * (Rᴴ * (R * Rᴴ)⁻¹)) * R)
    ∧ (∀ D : Matrix r r ℂ, N = Rᴴ * D * R →
        D = (Rᴴ * (R * Rᴴ)⁻¹)ᴴ * N * (Rᴴ * (R * Rᴴ)⁻¹)) := by
  have hzero : ((1 : Matrix w w ℂ) - Rᴴ * (R * Rᴴ)⁻¹ * R) * N = 0
      ∧ N * ((1 : Matrix w w ℂ) - Rᴴ * (R * Rᴴ)⁻¹ * R) = 0 := by
    set M₁ := ((1 : Matrix w w ℂ) - Rᴴ * (R * Rᴴ)⁻¹ * R) * N
    set M₂ := N * ((1 : Matrix w w ℂ) - Rᴴ * (R * Rᴴ)⁻¹ * R)
    have h₁ : (0 : ℂ) ≤ (M₁ᴴ * M₁).trace :=
      (Matrix.posSemidef_conjTranspose_mul_self M₁).trace_nonneg
    have h₂ : (0 : ℂ) ≤ (M₂ᴴ * M₂).trace :=
      (Matrix.posSemidef_conjTranspose_mul_self M₂).trace_nonneg
    have e₁ : (M₁ᴴ * M₁).trace = 0 := by
      have hle : (M₁ᴴ * M₁).trace ≤ 0 := by
        calc (M₁ᴴ * M₁).trace
            ≤ (M₁ᴴ * M₁).trace + (M₂ᴴ * M₂).trace :=
              le_add_of_nonneg_right h₂
          _ = 0 := hnull
      exact le_antisymm hle h₁
    have e₂ : (M₂ᴴ * M₂).trace = 0 := by
      have := hnull
      rw [e₁, zero_add] at this
      exact this
    exact ⟨Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp e₁,
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp e₂⟩
  -- from the null test, `N` is fixed by the projection on both
  -- sides, hence factors through the packet
  have hPN : Rᴴ * (R * Rᴴ)⁻¹ * R * N = N := by
    have h := hzero.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h.symm
  have hNP : N * (Rᴴ * (R * Rᴴ)⁻¹ * R) = N := by
    have h := hzero.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h.symm
  have hfac : N = Rᴴ
      * ((Rᴴ * (R * Rᴴ)⁻¹)ᴴ * N * (Rᴴ * (R * Rᴴ)⁻¹)) * R := by
    have hLh : (R * Rᴴ)ᴴ = R * Rᴴ := by
      rw [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hdagh : (Rᴴ * (R * Rᴴ)⁻¹)ᴴ = (R * Rᴴ)⁻¹ * R := by
      rw [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_nonsing_inv, hLh,
        Matrix.conjTranspose_conjTranspose]
    calc N = Rᴴ * (R * Rᴴ)⁻¹ * R * N := hPN.symm
      _ = Rᴴ * (R * Rᴴ)⁻¹ * R
          * (N * (Rᴴ * (R * Rᴴ)⁻¹ * R)) := by rw [hNP]
      _ = Rᴴ * ((Rᴴ * (R * Rᴴ)⁻¹)ᴴ * N * (Rᴴ * (R * Rᴴ)⁻¹))
          * R := by
          rw [hdagh]
          simp only [Matrix.mul_assoc]
  exact ⟨hfac, (sm_marked_dirac R N).1⟩

/-! ## `thm:SM-occurrence-Choi-source`: minimal support -/

open scoped ComplexOrder MatrixOrder in
set_option linter.unusedDecidableInType false in
/-- `thm:SM-occurrence-Choi-source`, minimal-support clause:
the canonical factor `Γ_occ = √J_occ` has exactly the support
of `J_occ` (`ℰ_occ^min = supp J_occ`): their kernels agree. -/
theorem occurrence_choi_minimal_support {d : Type*} [Fintype d]
    [DecidableEq d] (J : Matrix (d × d) (d × d) ℂ)
    (hJ : J.PosSemidef) :
    ∀ x : d × d → ℂ, (CFC.sqrt J *ᵥ x = 0 ↔ J *ᵥ x = 0) :=
  fun x => sqrt_mulVec_eq_zero_iff hJ x

end NCG
