/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.CompatibleStableAtlasNormResolvent
import RenewalGeometry.OperatorLimits.CompatibleStableAtlasSpectralProjections

/-!
# Self-adjointness of a continuum operator from a stable discretization

Paper `predictive_spectral_geometry`, `thm:supp-compact-spin-resolvent`, clause
`eq:supp-local-norm-resolvent` ("the same argument on a fixed smooth periodic coordinate
extension"): the continuum operator `D̂_g` is not given in advance as a self-adjoint operator;
it is a symmetric first-order operator on `H¹`, and the discrete approximation itself proves
that it is self-adjoint with domain `H¹` (the step "this places `u` in its adjoint domain,
which is `H¹`" of the paper's proof).

Setting (`StableDiscretization`): a Hilbert space `H` (`L²`), a Banach space `V` (`H¹`, in
Fourier coordinates) with an injective compact embedding `sobolev : V → H` with dense range whose
closed balls have closed images (true for every compact operator on a Hilbert space; checked
directly for the Fourier embedding), a continuous operator `op : V → H` (the differential
operator on `H¹`) which is symmetric, `⟪op a, sobolev b⟫ = ⟪sobolev a, op b⟫`, a dense subspace
`core ⊆ V` (trigonometric polynomials), and finite stages `(Hn n, stage n, embed n)` with
reconstructions satisfying (A1)–(A2) of `def:stable-spin-atlas` and the core condition (A3)
`W_h S_h ψ → ψ`, `W_h D_h S_h ψ → op ψ` on `core`.

* `exists_solution`: for every non-real `z` and every `f ∈ H` there is `a ∈ V` with
  `op a - z sobolev a = f` (weak limits of the discrete resolvents: collective compactness from
  (A1)–(A2), the closed-ball property puts the limit in `sobolev(V) = H¹`, (A3) and symmetry of
  the stages identify the equation, density of the core concludes).
* `limit`: the self-adjoint operator `D̂` with domain `range sobolev` (`H¹`) and
  `D̂ (sobolev a) = op a` (`limit_op_sobolev`), as `SelfAdjointResolventData`.
* `toAtlas`: the data form a `CompatibleStableAtlas` with limit `D̂`, hence
  `tendsto_norm_resolvent` (norm-resolvent convergence of `W_h (D_h - z)⁻¹ W_h^*`) and
  `tendsto_spectralProjection` (isolated bounded-energy spectral projections).
-/

open Filter Topology ComplexConjugate
open scoped InnerProductSpace

noncomputable section

namespace RenewalGeometry

universe u v w

/-- **A stable discretization of a symmetric operator on `H¹`** (the data of
`def:stable-spin-atlas` with the limit operator given only as a symmetric operator on `H¹`,
as on the periodic extension of `thm:supp-compact-spin-resolvent`). -/
structure StableDiscretization (H : Type u) (V : Type v) (Hn : ℕ → Type w)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
    [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)] where
  /-- The embedding `H¹ → L²`. -/
  sobolev : V →L[ℂ] H
  sobolev_compact : IsCompactOperator sobolev
  sobolev_injective : Function.Injective sobolev
  sobolev_denseRange : DenseRange sobolev
  /-- Images of closed balls are closed (weak compactness of balls of `H¹`). -/
  sobolev_closedBall : ∀ R : ℝ, IsClosed (sobolev '' Metric.closedBall 0 R)
  /-- The continuum operator on `H¹`. -/
  op : V →L[ℂ] H
  /-- Symmetry on `H¹`. -/
  op_symm : ∀ a b : V, ⟪op a, sobolev b⟫_ℂ = ⟪sobolev a, op b⟫_ℂ
  /-- The smooth core (in `H¹` coordinates). -/
  core : Submodule ℂ V
  core_dense : Dense (core : Set V)
  /-- The isometries `W_h`. -/
  embed : ∀ n, Hn n →ₗᵢ[ℂ] H
  /-- The stage operators `D_h`. -/
  stage : ∀ n, Hn n →L[ℂ] Hn n
  stage_selfAdjoint : ∀ n, IsSelfAdjoint (stage n)
  /-- (A1) `W_h W_h^* → I` strongly. -/
  embed_adjoint_tendsto : ∀ f : H,
    Tendsto (fun n => embed n (ContinuousLinearMap.adjoint (embed n).toContinuousLinearMap f))
      atTop (𝓝 f)
  discreteNorm : ∀ n, Hn n → ℝ
  discreteNorm_nonneg : ∀ n u, 0 ≤ discreteNorm n u
  reconstruct : ∀ n, Hn n →ₗ[ℂ] V
  reconstructConst : ℝ
  reconstructConst_nonneg : 0 ≤ reconstructConst
  /-- (A1) `‖I_h u‖_{H¹} ≤ C ‖u‖_{1,h}`. -/
  norm_reconstruct_le : ∀ n u, ‖reconstruct n u‖ ≤ reconstructConst * discreteNorm n u
  reconstructError : ℕ → ℝ
  reconstructError_nonneg : ∀ n, 0 ≤ reconstructError n
  reconstructError_tendsto : Tendsto reconstructError atTop (𝓝 0)
  /-- (A1) `‖I_h u - W_h u‖ ≤ ε_h ‖u‖_{1,h}`. -/
  norm_sobolev_reconstruct_sub_embed_le : ∀ n u,
    ‖sobolev (reconstruct n u) - embed n u‖ ≤ reconstructError n * discreteNorm n u
  graphConst : ℝ
  graphConst_nonneg : 0 ≤ graphConst
  /-- (A2) `‖u‖_{1,h} ≤ C (‖D_h u‖ + ‖u‖)`. -/
  discreteNorm_le : ∀ n u, discreteNorm n u ≤ graphConst * (‖stage n u‖ + ‖u‖)
  /-- The samples `S_h ψ`. -/
  sample : ∀ n, core → Hn n
  /-- (A3) `W_h S_h ψ → ψ`. -/
  embed_sample_tendsto : ∀ ψ : core,
    Tendsto (fun n => embed n (sample n ψ)) atTop (𝓝 (sobolev ψ))
  /-- (A3) `W_h D_h S_h ψ → D̂ ψ`. -/
  embed_stage_sample_tendsto : ∀ ψ : core,
    Tendsto (fun n => embed n (stage n (sample n ψ))) atTop (𝓝 (op ψ))

namespace StableDiscretization

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]

variable (D : StableDiscretization H V Hn)

/-! ### Uniqueness -/

/-- `⟪op a, sobolev a⟫` is real. -/
theorem im_inner_op_sobolev (a : V) : (⟪D.op a, D.sobolev a⟫_ℂ).im = 0 := by
  have h : ⟪D.op a, D.sobolev a⟫_ℂ = conj ⟪D.op a, D.sobolev a⟫_ℂ := by
    rw [inner_conj_symm]
    exact D.op_symm a a
  exact Complex.conj_eq_iff_im.mp h.symm

/-- `|Im z| ‖sobolev a‖ ≤ ‖op a - z sobolev a‖`. -/
theorem abs_im_mul_norm_le (a : V) (z : ℂ) :
    |z.im| * ‖D.sobolev a‖ ≤ ‖D.op a - z • D.sobolev a‖ :=
  RenewalGeometry.abs_im_mul_norm_le _ _ z (D.im_inner_op_sobolev a)

theorem eq_of_op_sub_eq {z : ℂ} (hz : z.im ≠ 0) {a b : V}
    (h : D.op a - z • D.sobolev a = D.op b - z • D.sobolev b) : a = b := by
  have h0 : D.op (a - b) - z • D.sobolev (a - b) = 0 := by
    rw [map_sub, map_sub, smul_sub, sub_sub_sub_comm, h, sub_self]
  have h1 := D.abs_im_mul_norm_le (a - b) z
  rw [h0, norm_zero] at h1
  have h2 : ‖D.sobolev (a - b)‖ = 0 := by
    have hp : 0 < |z.im| := abs_pos.mpr hz
    nlinarith [norm_nonneg (D.sobolev (a - b))]
  rw [norm_eq_zero, ← map_zero D.sobolev] at h2
  exact sub_eq_zero.mp (D.sobolev_injective h2)

/-! ### Existence: the discrete resolvents converge to a solution -/

/-- The stage resolvent `(D_h - z)⁻¹`. -/
def stageRes (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) : Hn n →L[ℂ] Hn n :=
  (SelfAdjointResolventData.ofBounded (D.stage n) (D.stage_selfAdjoint n)).resolvent z hz

theorem stage_stageRes (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) (g : Hn n) :
    D.stage n (D.stageRes n hz g) - z • D.stageRes n hz g = g :=
  SelfAdjointResolventData.ofBounded_apply_resolvent _ _ hz g

theorem norm_stageRes_le (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) (g : Hn n) :
    ‖D.stageRes n hz g‖ ≤ |z.im|⁻¹ * ‖g‖ :=
  (SelfAdjointResolventData.ofBounded (D.stage n) (D.stage_selfAdjoint n)).norm_resolvent_apply_le
    hz g

/-- The discrete approximate solutions `u_h = (D_h - z)⁻¹ W_h^* f`. -/
def approxSol {z : ℂ} (hz : z.im ≠ 0) (f : H) (n : ℕ) : Hn n :=
  D.stageRes n hz (ContinuousLinearMap.adjoint (D.embed n).toContinuousLinearMap f)

/-- Uniform first-order bound on the discrete approximate solutions (A2). -/
theorem discreteNorm_approxSol_le {z : ℂ} (hz : z.im ≠ 0) (f : H) (n : ℕ) :
    D.discreteNorm n (D.approxSol hz f n) ≤
      D.graphConst * ((1 + ‖z‖ * |z.im|⁻¹) * ‖f‖ + |z.im|⁻¹ * ‖f‖) := by
  set g := ContinuousLinearMap.adjoint (D.embed n).toContinuousLinearMap f
  set u := D.approxSol hz f n
  have hg : ‖g‖ ≤ ‖f‖ := norm_adjoint_isometry_apply_le _ f
  have hu : ‖u‖ ≤ |z.im|⁻¹ * ‖f‖ :=
    (D.norm_stageRes_le n hz g).trans (by gcongr)
  have hDu : ‖D.stage n u‖ ≤ (1 + ‖z‖ * |z.im|⁻¹) * ‖f‖ := by
    have h : D.stage n u = g + z • u := by
      have := D.stage_stageRes n hz g
      rw [← this]
      simp only [u, approxSol, g]
      abel
    rw [h]
    calc ‖g + z • u‖ ≤ ‖g‖ + ‖z‖ * ‖u‖ := (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ ‖f‖ + ‖z‖ * (|z.im|⁻¹ * ‖f‖) := by gcongr
      _ = (1 + ‖z‖ * |z.im|⁻¹) * ‖f‖ := by ring
  calc D.discreteNorm n u ≤ D.graphConst * (‖D.stage n u‖ + ‖u‖) := D.discreteNorm_le n u
    _ ≤ _ := by gcongr; exact D.graphConst_nonneg

/-- The discrete resolvent equation tested against samples:
`⟪f, W_h S_h ψ⟫ = ⟪W_h u_h, W_h D_h S_h ψ⟫ - z̄ ⟪W_h u_h, W_h S_h ψ⟫`. -/
theorem inner_embed_sample_eq {z : ℂ} (hz : z.im ≠ 0) (f : H) (n : ℕ) (s : Hn n) :
    ⟪f, D.embed n s⟫_ℂ = ⟪D.embed n (D.approxSol hz f n), D.embed n (D.stage n s)⟫_ℂ -
      conj z * ⟪D.embed n (D.approxSol hz f n), D.embed n s⟫_ℂ := by
  set W := (D.embed n).toContinuousLinearMap
  set u := D.approxSol hz f n
  have hres : D.stage n u - z • u = ContinuousLinearMap.adjoint W f := D.stage_stageRes n hz _
  have h1 : ⟪f, D.embed n s⟫_ℂ = ⟪ContinuousLinearMap.adjoint W f, s⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    rfl
  rw [h1, ← hres, inner_sub_left, inner_smul_left, LinearIsometry.inner_map_map,
    LinearIsometry.inner_map_map]
  congr 1
  have hsa := D.stage_selfAdjoint n
  rw [← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq]

/-- **Existence of solutions.**  For every non-real `z` and every `f`, the equation
`op a - z sobolev a = f` has a solution `a ∈ V` (`H¹`). -/
theorem exists_solution {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    ∃ a : V, D.op a - z • D.sobolev a = f := by
  set B := D.graphConst * ((1 + ‖z‖ * |z.im|⁻¹) * ‖f‖ + |z.im|⁻¹ * ‖f‖) with hB
  set R := D.reconstructConst * B
  set a : ℕ → V := fun n => D.reconstruct n (D.approxSol hz f n)
  have ha : ∀ n, a n ∈ Metric.closedBall (0 : V) R := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (D.norm_reconstruct_le n _).trans
      (mul_le_mul_of_nonneg_left (D.discreteNorm_approxSol_le hz f n) D.reconstructConst_nonneg)
  obtain ⟨K, hK, hKsub⟩ := D.sobolev_compact.image_closedBall_subset_compact R
  obtain ⟨u, -, φ, hφ, hu⟩ := hK.tendsto_subseq (x := fun n => D.sobolev (a n))
    (fun n => hKsub ⟨a n, ha n, rfl⟩)
  -- the limit lies in `sobolev(V)`
  obtain ⟨a₀, -, rfl⟩ : u ∈ D.sobolev '' Metric.closedBall 0 R :=
    (D.sobolev_closedBall R).mem_of_tendsto hu
      (Eventually.of_forall fun k => ⟨a (φ k), ha (φ k), rfl⟩)
  -- the embedded discrete solutions converge to the same limit
  have herr : Tendsto (fun n => ‖D.sobolev (a n) - D.embed n (D.approxSol hz f n)‖) atTop
      (𝓝 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n =>
      (D.norm_sobolev_reconstruct_sub_embed_le n _).trans
        (mul_le_mul_of_nonneg_left (D.discreteNorm_approxSol_le hz f n)
          (D.reconstructError_nonneg n))) ?_
    simpa using D.reconstructError_tendsto.mul_const B
  have hW : Tendsto (fun k => D.embed (φ k) (D.approxSol hz f (φ k))) atTop
      (𝓝 (D.sobolev a₀)) := by
    have h2 := (herr.comp hφ.tendsto_atTop)
    have h3 : Tendsto (fun k => D.sobolev (a (φ k)) -
        D.embed (φ k) (D.approxSol hz f (φ k))) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr h2
    have := hu.sub h3
    rw [sub_zero] at this
    exact this.congr fun k => sub_sub_cancel _ _
  refine ⟨a₀, ?_⟩
  -- the residual is orthogonal to the dense set `sobolev(core)`
  set g := D.op a₀ - z • D.sobolev a₀ - f
  have horth : ∀ ψ : D.core, ⟪g, D.sobolev ψ⟫_ℂ = 0 := by
    intro ψ
    have hL : Tendsto (fun k => ⟪f, D.embed (φ k) (D.sample (φ k) ψ)⟫_ℂ) atTop
        (𝓝 ⟪f, D.sobolev ψ⟫_ℂ) :=
      tendsto_const_nhds.inner ((D.embed_sample_tendsto ψ).comp hφ.tendsto_atTop)
    have hR : Tendsto (fun k => ⟪D.embed (φ k) (D.approxSol hz f (φ k)),
          D.embed (φ k) (D.stage (φ k) (D.sample (φ k) ψ))⟫_ℂ -
        conj z * ⟪D.embed (φ k) (D.approxSol hz f (φ k)),
          D.embed (φ k) (D.sample (φ k) ψ)⟫_ℂ) atTop
        (𝓝 (⟪D.sobolev a₀, D.op ψ⟫_ℂ - conj z * ⟪D.sobolev a₀, D.sobolev ψ⟫_ℂ)) :=
      (hW.inner ((D.embed_stage_sample_tendsto ψ).comp hφ.tendsto_atTop)).sub
        ((hW.inner ((D.embed_sample_tendsto ψ).comp hφ.tendsto_atTop)).const_mul _)
    have heq : ⟪f, D.sobolev ψ⟫_ℂ =
        ⟪D.sobolev a₀, D.op ψ⟫_ℂ - conj z * ⟪D.sobolev a₀, D.sobolev ψ⟫_ℂ := by
      refine tendsto_nhds_unique hL (hR.congr fun k => ?_)
      exact (D.inner_embed_sample_eq hz f (φ k) _).symm
    simp only [g, inner_sub_left, inner_smul_left]
    rw [D.op_symm, heq]
    ring
  -- density
  have hdense : Dense (D.sobolev '' (D.core : Set V)) := by
    have h1 : Set.range D.sobolev ⊆ closure (D.sobolev '' (D.core : Set V)) := by
      rintro _ ⟨b, rfl⟩
      have hb : b ∈ closure (D.core : Set V) := D.core_dense b
      exact image_closure_subset_closure_image D.sobolev.continuous ⟨b, hb, rfl⟩
    intro x
    exact closure_minimal h1 isClosed_closure (D.sobolev_denseRange x)
  have hclosed : IsClosed {x : H | ⟪g, x⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hall : ∀ x : H, ⟪g, x⟫_ℂ = 0 := by
    intro x
    have hsub : D.sobolev '' (D.core : Set V) ⊆ {x : H | ⟪g, x⟫_ℂ = 0} := by
      rintro _ ⟨b, hb, rfl⟩
      exact horth ⟨b, hb⟩
    exact closure_minimal hsub hclosed (hdense x)
  have hg : g = 0 := inner_self_eq_zero.mp (hall g)
  exact sub_eq_zero.mp hg

/-! ### The self-adjoint operator `D̂` with domain `H¹` -/

/-- The domain `H¹ = range sobolev`. -/
def domain : Submodule ℂ H := LinearMap.range D.sobolev.toLinearMap

theorem sobolev_mem_domain (a : V) : D.sobolev a ∈ D.domain := ⟨a, rfl⟩

/-- `V ≃ H¹` through the injective embedding. -/
def domainEquiv : V ≃ₗ[ℂ] D.domain :=
  LinearEquiv.ofInjective D.sobolev.toLinearMap D.sobolev_injective

theorem domainEquiv_apply (a : V) : (D.domainEquiv a : H) = D.sobolev a := rfl

/-- The operator `D̂ : H¹ → L²`, `D̂ (sobolev a) = op a`. -/
def limitOp : H →ₗ.[ℂ] H :=
  ⟨D.domain, D.op.toLinearMap ∘ₗ D.domainEquiv.symm.toLinearMap⟩

theorem limitOp_domain : D.limitOp.domain = D.domain := rfl

/-- **`D̂` on `H¹`**: `D̂ (sobolev a) = op a`. -/
theorem limitOp_sobolev (a : V) : D.limitOp ⟨D.sobolev a, D.sobolev_mem_domain a⟩ = D.op a := by
  change D.op (D.domainEquiv.symm ⟨D.sobolev a, _⟩) = D.op a
  congr 1
  apply D.domainEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem limitOp_apply (x : D.limitOp.domain) :
    D.limitOp x = D.op (D.domainEquiv.symm x) := rfl

theorem sobolev_domainEquiv_symm (x : D.domain) :
    D.sobolev (D.domainEquiv.symm x) = x :=
  congrArg Subtype.val (D.domainEquiv.apply_symm_apply x)

/-- Symmetry of `D̂` on `H¹`. -/
theorem limitOp_isFormalAdjoint : D.limitOp.IsFormalAdjoint D.limitOp := by
  intro x y
  rw [D.limitOp_apply, D.limitOp_apply]
  conv_lhs => rw [← D.sobolev_domainEquiv_symm y]
  conv_rhs => rw [← D.sobolev_domainEquiv_symm x]
  exact D.op_symm _ _

/-- The solution operator `f ↦ a` of `op a - z sobolev a = f`. -/
def solution {z : ℂ} (hz : z.im ≠ 0) (f : H) : V := (D.exists_solution hz f).choose

theorem solution_spec {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    D.op (D.solution hz f) - z • D.sobolev (D.solution hz f) = f :=
  (D.exists_solution hz f).choose_spec

theorem solution_eq {z : ℂ} (hz : z.im ≠ 0) (a : V) :
    D.solution hz (D.op a - z • D.sobolev a) = a :=
  D.eq_of_op_sub_eq hz (D.solution_spec hz _)

/-- The resolvent as a linear map `f ↦ sobolev a`. -/
def resolventLin {z : ℂ} (hz : z.im ≠ 0) : H →ₗ[ℂ] H where
  toFun f := D.sobolev (D.solution hz f)
  map_add' f g := by
    rw [← map_add]
    congr 1
    apply D.eq_of_op_sub_eq hz
    rw [D.solution_spec, map_add, map_add, smul_add]
    have h1 := D.solution_spec hz f
    have h2 := D.solution_spec hz g
    rw [← sub_add_sub_comm, h1, h2]
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    apply D.eq_of_op_sub_eq hz
    rw [D.solution_spec, map_smul, map_smul, smul_comm z c, ← smul_sub, D.solution_spec]

theorem norm_resolventLin_le {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    ‖D.resolventLin hz f‖ ≤ |z.im|⁻¹ * ‖f‖ := by
  have hp : 0 < |z.im| := abs_pos.mpr hz
  have h := D.abs_im_mul_norm_le (D.solution hz f) z
  rw [D.solution_spec] at h
  change ‖D.sobolev (D.solution hz f)‖ ≤ _
  rw [inv_mul_eq_div, le_div_iff₀ hp]
  linarith

/-- The resolvent `(D̂ - z)⁻¹`. -/
def resolvent {z : ℂ} (hz : z.im ≠ 0) : H →L[ℂ] H :=
  (D.resolventLin hz).mkContinuous |z.im|⁻¹ (D.norm_resolventLin_le hz)

theorem resolvent_apply {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    D.resolvent hz f = D.sobolev (D.solution hz f) := rfl

/-- **The self-adjoint realisation `D̂`** with domain `H¹ = range sobolev`, presented by its
resolvents (`op - z` is onto for non-real `z` by `exists_solution`). -/
def limit : SelfAdjointResolventData H where
  op := D.limitOp
  symm := D.limitOp_isFormalAdjoint
  resolvent z hz := D.resolvent hz
  resolvent_mem z hz f := D.sobolev_mem_domain _
  op_resolvent z hz f := by
    change D.limitOp ⟨D.sobolev (D.solution hz f), D.sobolev_mem_domain _⟩ - z • _ = f
    rw [D.limitOp_sobolev]
    exact D.solution_spec hz f
  resolvent_op z hz x := by
    change D.sobolev (D.solution hz (D.limitOp x - z • (x : H))) = x
    rw [D.limitOp_apply]
    have hx := D.sobolev_domainEquiv_symm x
    conv_lhs => rw [← hx]
    rw [D.solution_eq]
    exact hx

@[simp] theorem limit_op : D.limit.op = D.limitOp := rfl

/-- The domain of `D̂` is `H¹`. -/
theorem limit_domain : D.limit.op.domain = LinearMap.range D.sobolev.toLinearMap := rfl

/-- `D̂ (sobolev a) = op a`. -/
theorem limit_op_sobolev (a : V) :
    D.limit.op ⟨D.sobolev a, D.sobolev_mem_domain a⟩ = D.op a := D.limitOp_sobolev a

/-- `D̂` is self-adjoint in Mathlib's sense (`LinearPMap.adjoint`). -/
theorem isSelfAdjoint_limit : IsSelfAdjoint D.limit.op := D.limit.isSelfAdjoint_op

/-! ### The compatible stable atlas -/

/-- The smooth core inside `H¹ ⊆ L²`. -/
def coreH : Submodule ℂ H := D.core.map D.sobolev.toLinearMap

theorem coreH_spec (ψ : D.coreH) : ∃ a, a ∈ D.core ∧ D.sobolev a = ψ := ψ.2

/-- A preimage in `core` of a vector of `coreH`. -/
def corePre (ψ : D.coreH) : D.core :=
  ⟨(D.coreH_spec ψ).choose, (D.coreH_spec ψ).choose_spec.1⟩

theorem sobolev_corePre (ψ : D.coreH) : D.sobolev (D.corePre ψ) = ψ :=
  (D.coreH_spec ψ).choose_spec.2

theorem coreH_le : D.coreH ≤ D.limit.op.domain := by
  rintro _ ⟨a, -, rfl⟩
  exact D.sobolev_mem_domain a

/-- **The data form a compatible stable atlas** (`def:stable-spin-atlas`) whose limit is the
self-adjoint realisation `D̂` with domain `H¹`. -/
def toAtlas : CompatibleStableAtlas H V Hn where
  limit := D.limit
  core := D.coreH
  core_le := D.coreH_le
  core_dense u := by
    obtain ⟨a, ha⟩ : ∃ a, D.sobolev a = (u : H) := u.2
    obtain ⟨c, hc, hca⟩ := mem_closure_iff_seq_limit.mp (D.core_dense a)
    refine ⟨fun k => ⟨D.sobolev (c k), D.sobolev_mem_domain _⟩, fun k => ⟨c k, hc k, rfl⟩,
      ?_, ?_⟩
    · rw [← ha]
      exact (D.sobolev.continuous.tendsto a).comp hca
    · have hu : u = ⟨D.sobolev a, D.sobolev_mem_domain a⟩ := Subtype.ext ha.symm
      rw [hu]
      change Tendsto (fun k => D.limitOp ⟨D.sobolev (c k), _⟩) atTop
        (𝓝 (D.limitOp ⟨D.sobolev a, _⟩))
      simp_rw [D.limitOp_sobolev]
      exact (D.op.continuous.tendsto a).comp hca
  sobolev := D.sobolev
  sobolev_compact := D.sobolev_compact
  embed := D.embed
  stage := D.stage
  stage_selfAdjoint := D.stage_selfAdjoint
  embed_adjoint_tendsto := D.embed_adjoint_tendsto
  discreteNorm := D.discreteNorm
  discreteNorm_nonneg := D.discreteNorm_nonneg
  reconstruct := D.reconstruct
  reconstructConst := D.reconstructConst
  reconstructConst_nonneg := D.reconstructConst_nonneg
  norm_reconstruct_le := D.norm_reconstruct_le
  reconstructError := D.reconstructError
  reconstructError_nonneg := D.reconstructError_nonneg
  reconstructError_tendsto := D.reconstructError_tendsto
  norm_sobolev_reconstruct_sub_embed_le := D.norm_sobolev_reconstruct_sub_embed_le
  graphConst := D.graphConst
  graphConst_nonneg := D.graphConst_nonneg
  discreteNorm_le := D.discreteNorm_le
  sample n ψ := D.sample n (D.corePre ψ)
  embed_sample_tendsto ψ := by
    have := D.embed_sample_tendsto (D.corePre ψ)
    rwa [D.sobolev_corePre] at this
  embed_stage_sample_tendsto ψ := by
    have h := D.embed_stage_sample_tendsto (D.corePre ψ)
    have hψ : (⟨ψ, D.coreH_le ψ.2⟩ : D.limit.op.domain) =
        ⟨D.sobolev (D.corePre ψ), D.sobolev_mem_domain _⟩ :=
      Subtype.ext (D.sobolev_corePre ψ).symm
    rw [hψ, D.limit_op_sobolev]
    exact h

@[simp] theorem toAtlas_limit : D.toAtlas.limit = D.limit := rfl

/-- **Norm-resolvent convergence** (`eq:supp-global-norm-resolvent` /
`eq:supp-local-norm-resolvent` for the self-adjoint realisation on `H¹`):
`‖W_h (D_h - z)⁻¹ W_h^* - (D̂ - z)⁻¹‖ → 0` for every non-real `z`. -/
theorem tendsto_norm_resolvent {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun n => ‖(D.embed n).toContinuousLinearMap ∘L D.stageRes n hz ∘L
        ContinuousLinearMap.adjoint (D.embed n).toContinuousLinearMap - D.limit.resolvent z hz‖)
      atTop (𝓝 0) :=
  D.toAtlas.tendsto_norm_embeddedResolvent_sub hz

/-- The limit resolvent is compact. -/
theorem isCompactOperator_resolvent {z : ℂ} (hz : z.im ≠ 0) :
    IsCompactOperator (D.limit.resolvent z hz) :=
  D.toAtlas.isCompactOperator_limit_resolvent hz

/-- **Spectral projections**: for a bounded window `(a,b)` whose endpoints are not eigenvalues of
`D̂`, `‖W_h 1_{(a,b)}(D_h) W_h^* - 1_{(a,b)}(D̂)‖ → 0`. -/
theorem tendsto_norm_spectralProjection {a b : ℝ} (hab : a < b)
    (ha : D.limit.opEigenspace (a : ℂ) = ⊥) (hb : D.limit.opEigenspace (b : ℂ) = ⊥) :
    Tendsto (fun n => ‖D.toAtlas.embeddedSpectralProjection a b n -
      D.limit.spectralProjection a b‖) atTop (𝓝 0) :=
  D.toAtlas.tendsto_norm_embeddedSpectralProjection_sub hab ha hb

end StableDiscretization

end RenewalGeometry
