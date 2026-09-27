/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.UnboundedSelfAdjointResolvent
import RenewalGeometry.OperatorLimits.CollectivelyCompactStrongAdjointToNorm
import RenewalGeometry.OperatorLimits.CompactScreenCollectiveCompactness
import RenewalGeometry.OperatorLimits.DenseSourceStrongConvergence
import RenewalGeometry.OperatorLimits.RieszProjectionStability
import RenewalGeometry.OperatorLimits.ContourResolventBounds

/-!
# Norm-resolvent convergence for compatible stable atlases

Paper `predictive_spectral_geometry`, labels `def:stable-spin-atlas`,
`thm:supp-compact-spin-resolvent` and the spin clause of `thm:compact-spin-main`, in the
abstract surrogate the paper's proof uses.

* `CompatibleStableAtlas` (`def:stable-spin-atlas`): a fixed Hilbert space `H` (surrogate for
  `L²(M; S ⊗ ℂ²)`), an unbounded self-adjoint operator `limit` given by its resolvents
  (surrogate for `D̂ = D_{M,𝔰} ⊗ σ₁`), a subspace `core` (the smooth doubled spinors) which is a
  core for `limit`, a Banach space `V` with a compact embedding `sobolev : V → H` (surrogate
  for `H¹(M; S ⊗ ℂ²) ↪ L²`, Rellich), finite-dimensional stage Hilbert spaces `Hn n` with
  self-adjoint stage operators `stage n` (`D_h`) and isometries `embed n` (`W_h`), and the
  axioms (A1)–(A3) as fields: `W_h W_h^* → I` strongly, reconstructions `I_h : ℋ_h → V` with
  `‖I_h u‖_V ≤ C ‖u‖_{1,h}` and `‖I_h u - W_h u‖ ≤ ε_h ‖u‖_{1,h}`, the assembled graph estimate
  `‖u‖_{1,h} ≤ C (‖D_h u‖ + ‖u‖)`, and samples `S_h ψ` of core vectors with
  `W_h S_h ψ → ψ`, `W_h D_h S_h ψ → D̂ ψ`.
* `tendsto_embeddedResolvent_apply`: strong resolvent convergence
  `W_h (D_h - z)⁻¹ W_h^* f → (D̂ - z)⁻¹ f` from (A3) by the core argument, using the uniform
  bounds `eq:uniform-resolvent-bounds` and density of `(D̂ - z)(core)`.
* `collectivelyCompact_embeddedResolvent`: (A1)–(A2) and the compact embedding give collective
  compactness of the embedded resolvents (the Rellich step).
* `tendsto_embeddedResolvent` (**`eq:supp-global-norm-resolvent`**,
  **`eq:compact-spin-resolvent-main`**): `‖W_h (D_h - z)⁻¹ W_h^* - (D̂ - z)⁻¹‖ → 0` for every
  non-real `z`, with compact limit resolvent, via the strong-plus-adjoint-to-norm upgrade of
  `CollectivelyCompactStrongAdjointToNorm`.
* `circleRieszProjection_embeddedResolvent_tendsto`: the spectral-projection clause, in
  resolvent form: Riesz projections of the compressed resolvents on any circle in the resolvent
  set of `(D̂ - z)⁻¹` converge in norm.

The periodic-extension clause `eq:supp-local-norm-resolvent` is the same theorem applied to the
periodic-extension atlas; the real and grading structures are not encoded.
-/

open Filter Topology ComplexConjugate
open scoped InnerProductSpace

noncomputable section

namespace RenewalGeometry

open VaryingHilbert

universe u v w

/-! ### Isometry helpers -/

section isometry

variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

/-- `W^* W = 1` for an isometry `W`. -/
theorem adjoint_isometry_apply_map (W : E →ₗᵢ[ℂ] F) (x : E) :
    ContinuousLinearMap.adjoint W.toContinuousLinearMap (W x) = x := by
  apply ext_inner_right ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact W.inner_map_map x v

/-- `‖W^* f‖ ≤ ‖f‖` for an isometry `W`. -/
theorem norm_adjoint_isometry_apply_le (W : E →ₗᵢ[ℂ] F) (f : F) :
    ‖ContinuousLinearMap.adjoint W.toContinuousLinearMap f‖ ≤ ‖f‖ := by
  calc ‖ContinuousLinearMap.adjoint W.toContinuousLinearMap f‖
      ≤ ‖ContinuousLinearMap.adjoint W.toContinuousLinearMap‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ f
    _ ≤ 1 * ‖f‖ := by
        gcongr
        rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
        exact W.norm_toContinuousLinearMap_le
    _ = ‖f‖ := one_mul _

end isometry

/-! ### The compatible stable atlas -/

/-- **`def:stable-spin-atlas`** (abstract surrogate).  The continuum data are a Hilbert space
`H`, a self-adjoint operator `limit` (presented by its resolvents) with a core `core`, and a
compact embedding `sobolev : V → H` of a Banach space playing the role of `H¹`.  The discrete
data are finite-dimensional stage Hilbert spaces `Hn n`, self-adjoint stage operators `stage n`,
isometries `embed n`, discrete first-order norms `discreteNorm n`, reconstructions
`reconstruct n : Hn n → V`, and samples `sample n : core → Hn n`, subject to (A1)–(A3). -/
structure CompatibleStableAtlas (H : Type u) (V : Type v) (Hn : ℕ → Type w)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
    [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)] where
  /-- The limiting self-adjoint operator `D̂`. -/
  limit : SelfAdjointResolventData H
  /-- The smooth core (smooth doubled spinors). -/
  core : Submodule ℂ H
  core_le : core ≤ limit.op.domain
  /-- `core` is a core for `limit`: every domain vector is a graph-limit of core vectors. -/
  core_dense : ∀ u : limit.op.domain, ∃ ψ : ℕ → limit.op.domain,
    (∀ k, (ψ k : H) ∈ core) ∧ Tendsto (fun k => (ψ k : H)) atTop (𝓝 (u : H)) ∧
      Tendsto (fun k => limit.op (ψ k)) atTop (𝓝 (limit.op u))
  /-- The compact Sobolev embedding `H¹ → L²` (Rellich). -/
  sobolev : V →L[ℂ] H
  sobolev_compact : IsCompactOperator sobolev
  /-- The isometries `W_h : ℋ_h → ℋ`. -/
  embed : ∀ n, Hn n →ₗᵢ[ℂ] H
  /-- The stage operators `D_h`. -/
  stage : ∀ n, Hn n →L[ℂ] Hn n
  stage_selfAdjoint : ∀ n, IsSelfAdjoint (stage n)
  /-- (A1) `W_h W_h^* → I` strongly. -/
  embed_adjoint_tendsto : ∀ f : H,
    Tendsto (fun n => embed n (ContinuousLinearMap.adjoint (embed n).toContinuousLinearMap f))
      atTop (𝓝 f)
  /-- The discrete first-order norms `‖·‖_{1,h}`. -/
  discreteNorm : ∀ n, Hn n → ℝ
  discreteNorm_nonneg : ∀ n u, 0 ≤ discreteNorm n u
  /-- The reconstructions `I_h : ℋ_h → H¹`. -/
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
  /-- (A2) the assembled graph estimate `‖u‖_{1,h} ≤ C (‖D_h u‖_h + ‖u‖_h)`. -/
  discreteNorm_le : ∀ n u, discreteNorm n u ≤ graphConst * (‖stage n u‖ + ‖u‖)
  /-- The samples `S_h ψ` of core vectors. -/
  sample : ∀ n, core → Hn n
  /-- (A3) `W_h S_h ψ → ψ`. -/
  embed_sample_tendsto : ∀ ψ : core,
    Tendsto (fun n => embed n (sample n ψ)) atTop (𝓝 (ψ : H))
  /-- (A3) `W_h D_h S_h ψ → D̂ ψ`. -/
  embed_stage_sample_tendsto : ∀ ψ : core,
    Tendsto (fun n => embed n (stage n (sample n ψ))) atTop (𝓝 (limit.op ⟨ψ, core_le ψ.2⟩))

namespace CompatibleStableAtlas

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]

variable (A : CompatibleStableAtlas H V Hn)

/-- The stage operator `D_h` as resolvent data. -/
def stageData (n : ℕ) : SelfAdjointResolventData (Hn n) :=
  SelfAdjointResolventData.ofBounded (A.stage n) (A.stage_selfAdjoint n)

/-- The stage resolvent `(D_h - z)⁻¹`. -/
def stageResolvent (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) : Hn n →L[ℂ] Hn n :=
  (A.stageData n).resolvent z hz

/-- The embedded (compressed) resolvent `R_h(z) = W_h (D_h - z)⁻¹ W_h^*`. -/
def embeddedResolvent (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) : H →L[ℂ] H :=
  (A.embed n).toContinuousLinearMap ∘L A.stageResolvent n z hz ∘L
    ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap

theorem embeddedResolvent_apply (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) (f : H) :
    A.embeddedResolvent z hz n f =
      A.embed n (A.stageResolvent n z hz
        (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f)) := rfl

/-- `(D_h - z)⁻¹ (D_h x - z x) = x`. -/
theorem stageResolvent_apply_sub (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) (x : Hn n) :
    A.stageResolvent n z hz (A.stage n x - z • x) = x :=
  SelfAdjointResolventData.ofBounded_resolvent_apply_sub _ _ hz x

/-- `D_h (D_h - z)⁻¹ f - z (D_h - z)⁻¹ f = f`. -/
theorem stage_stageResolvent (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) (f : Hn n) :
    A.stage n (A.stageResolvent n z hz f) - z • A.stageResolvent n z hz f = f :=
  SelfAdjointResolventData.ofBounded_apply_resolvent _ _ hz f

/-- **`eq:uniform-resolvent-bounds`** at stage level. -/
theorem norm_stageResolvent_apply_le (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) (x : Hn n) :
    ‖A.stageResolvent n z hz x‖ ≤ |z.im|⁻¹ * ‖x‖ :=
  (A.stageData n).norm_resolvent_apply_le hz x

theorem norm_embeddedResolvent_apply_le {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) (f : H) :
    ‖A.embeddedResolvent z hz n f‖ ≤ |z.im|⁻¹ * ‖f‖ := by
  rw [embeddedResolvent_apply, LinearIsometry.norm_map]
  calc _ ≤ |z.im|⁻¹ * ‖ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f‖ :=
        A.norm_stageResolvent_apply_le n hz _
    _ ≤ |z.im|⁻¹ * ‖f‖ := by
        gcongr
        exact norm_adjoint_isometry_apply_le _ f

/-- The compressed resolvents are uniformly bounded by `|Im z|⁻¹`. -/
theorem norm_embeddedResolvent_le {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    ‖A.embeddedResolvent z hz n‖ ≤ |z.im|⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (abs_nonneg _))
    fun f => A.norm_embeddedResolvent_apply_le hz n f

/-- The adjoint of the compressed resolvent at `z` is the compressed resolvent at `z̄`. -/
theorem adjoint_embeddedResolvent {z : ℂ} (hz : z.im ≠ 0) (hz' : (conj z).im ≠ 0) (n : ℕ) :
    ContinuousLinearMap.adjoint (A.embeddedResolvent z hz n) =
      A.embeddedResolvent (conj z) hz' n := by
  unfold embeddedResolvent
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ← ContinuousLinearMap.comp_assoc]
  congr 2
  exact (A.stageData n).adjoint_resolvent hz hz'

/-! ### Strong resolvent convergence from the core condition (A3) -/

/-- The core vector `ψ` as a domain vector of the limit operator. -/
def coreToDomain (ψ : A.core) : A.limit.op.domain := ⟨ψ, A.core_le ψ.2⟩

/-- The error `(D_h - z)⁻¹ W_h^* (D̂ - z) ψ - S_h ψ` is controlled by the two (A3) defects. -/
theorem norm_stageResolvent_core_sub_sample_le {z : ℂ} (hz : z.im ≠ 0) (ψ : A.core) (n : ℕ) :
    ‖A.stageResolvent n z hz (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap
        (A.limit.op (A.coreToDomain ψ) - z • (ψ : H))) - A.sample n ψ‖ ≤
      |z.im|⁻¹ * (‖A.limit.op (A.coreToDomain ψ) - A.embed n (A.stage n (A.sample n ψ))‖ +
        ‖z‖ * ‖(ψ : H) - A.embed n (A.sample n ψ)‖) := by
  set W := (A.embed n).toContinuousLinearMap
  set s := A.sample n ψ
  set a : H := A.limit.op (A.coreToDomain ψ) - A.embed n (A.stage n s)
  set b : H := (ψ : H) - A.embed n s
  have hid : ContinuousLinearMap.adjoint W (A.limit.op (A.coreToDomain ψ) - z • (ψ : H))
      - (A.stage n s - z • s) =
      ContinuousLinearMap.adjoint W a - z • ContinuousLinearMap.adjoint W b := by
    simp only [a, b, map_sub, map_smul, W, adjoint_isometry_apply_map, smul_sub]
    abel
  have hsub : A.stageResolvent n z hz (ContinuousLinearMap.adjoint W
      (A.limit.op (A.coreToDomain ψ) - z • (ψ : H))) - s =
      A.stageResolvent n z hz (ContinuousLinearMap.adjoint W a
        - z • ContinuousLinearMap.adjoint W b) := by
    rw [← hid, map_sub (A.stageResolvent n z hz), A.stageResolvent_apply_sub n hz s]
  rw [hsub]
  calc ‖A.stageResolvent n z hz (ContinuousLinearMap.adjoint W a
        - z • ContinuousLinearMap.adjoint W b)‖
      ≤ |z.im|⁻¹ * ‖ContinuousLinearMap.adjoint W a - z • ContinuousLinearMap.adjoint W b‖ :=
        A.norm_stageResolvent_apply_le n hz _
    _ ≤ |z.im|⁻¹ * (‖a‖ + ‖z‖ * ‖b‖) := by
        gcongr
        calc ‖ContinuousLinearMap.adjoint W a - z • ContinuousLinearMap.adjoint W b‖
            ≤ ‖ContinuousLinearMap.adjoint W a‖ + ‖z • ContinuousLinearMap.adjoint W b‖ :=
              norm_sub_le _ _
          _ ≤ ‖a‖ + ‖z‖ * ‖b‖ := by
              rw [norm_smul]
              gcongr
              · exact norm_adjoint_isometry_apply_le _ a
              · exact norm_adjoint_isometry_apply_le _ b

/-- Strong convergence of the compressed resolvents on `(D̂ - z)(core)`. -/
theorem tendsto_embeddedResolvent_core {z : ℂ} (hz : z.im ≠ 0) (ψ : A.core) :
    Tendsto (fun n => A.embeddedResolvent z hz n (A.limit.op (A.coreToDomain ψ) - z • (ψ : H)))
      atTop (𝓝 (ψ : H)) := by
  set g : H := A.limit.op (A.coreToDomain ψ) - z • (ψ : H)
  set e : ∀ n, Hn n := fun n =>
    A.stageResolvent n z hz (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap g)
      - A.sample n ψ
  have ha : Tendsto
      (fun n => ‖A.limit.op (A.coreToDomain ψ) - A.embed n (A.stage n (A.sample n ψ))‖)
      atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := A.limit.op (A.coreToDomain ψ))).sub
      (A.embed_stage_sample_tendsto ψ)).norm
    simpa [coreToDomain] using this
  have hb : Tendsto (fun n => ‖(ψ : H) - A.embed n (A.sample n ψ)‖) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (ψ : H))).sub (A.embed_sample_tendsto ψ)).norm
    simpa using this
  have he : Tendsto (fun n => ‖e n‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => A.norm_stageResolvent_core_sub_sample_le hz ψ n) ?_
    have := ((ha.add (hb.const_mul ‖z‖)).const_mul (|z.im|⁻¹))
    simpa using this
  have hWe : Tendsto (fun n => A.embed n (e n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [LinearIsometry.norm_map] using he
  have hsum := hWe.add (A.embed_sample_tendsto ψ)
  rw [zero_add] at hsum
  refine hsum.congr fun n => ?_
  rw [embeddedResolvent_apply]
  simp only [e]
  rw [← map_add, sub_add_cancel]

/-- The set `(D̂ - z)(core)` is dense: the core is a core and `D̂ - z` is onto. -/
theorem dense_core_shifted_range {z : ℂ} (hz : z.im ≠ 0) :
    Dense (Set.range fun ψ : A.core => A.limit.op (A.coreToDomain ψ) - z • (ψ : H)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro f
  set u : A.limit.op.domain := ⟨A.limit.resolvent z hz f, A.limit.resolvent_mem z hz f⟩
  obtain ⟨ψ, hψmem, hψ, hDψ⟩ := A.core_dense u
  have hlim : Tendsto (fun k => A.limit.op (ψ k) - z • (ψ k : H)) atTop (𝓝 f) := by
    have := hDψ.sub (hψ.const_smul z)
    rwa [A.limit.op_resolvent z hz f] at this
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ⟨⟨ψ k, hψmem k⟩, ?_⟩)
  have : A.coreToDomain ⟨(ψ k : H), hψmem k⟩ = ψ k := Subtype.ext rfl
  change A.limit.op (A.coreToDomain ⟨(ψ k : H), hψmem k⟩) - z • (ψ k : H) = _
  rw [this]

/-- **Strong resolvent convergence.** `W_h (D_h - z)⁻¹ W_h^* f → (D̂ - z)⁻¹ f` for every `f`. -/
theorem tendsto_embeddedResolvent_apply {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    Tendsto (fun n => A.embeddedResolvent z hz n f) atTop (𝓝 (A.limit.resolvent z hz f)) := by
  have hconv := System.strongOperatorConverges_of_dense_sources_of_uniform_opNorm
    (constantSystem ℂ H) (constantSystem ℂ H) (A.embeddedResolvent z hz) (A.limit.resolvent z hz)
    (Set.range fun ψ : A.core => A.limit.op (A.coreToDomain ψ) - z • (ψ : H))
    (A.dense_core_shifted_range hz) (fun d _ => d)
    (fun d _ => by
      rw [System.constantSystem_stronglyConverges_iff]
      exact tendsto_const_nhds)
    |z.im|⁻¹ (inv_nonneg.mpr (abs_nonneg _)) (fun n => A.norm_embeddedResolvent_le hz n)
    (by
      rintro d ⟨ψ, rfl⟩
      rw [System.constantSystem_stronglyConverges_iff]
      have h := A.limit.resolvent_op z hz (A.coreToDomain ψ)
      change A.limit.resolvent z hz (A.limit.op (A.coreToDomain ψ) - z • (ψ : H)) = (ψ : H) at h
      rw [h]
      exact A.tendsto_embeddedResolvent_core hz ψ)
  have := hconv (fun _ => f) f (by
    rw [System.constantSystem_stronglyConverges_iff]
    exact tendsto_const_nhds)
  rwa [System.constantSystem_stronglyConverges_iff] at this

/-! ### Collective compactness from (A1)–(A2) and the compact embedding -/

/-- The discrete first-order norm of `(D_h - z)⁻¹ W_h^* f` is bounded uniformly on the unit
ball, by the graph estimate (A2) and `eq:uniform-resolvent-bounds`. -/
theorem discreteNorm_stageResolvent_le {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) (f : H) (hf : ‖f‖ ≤ 1) :
    A.discreteNorm n (A.stageResolvent n z hz
        (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f)) ≤
      A.graphConst * ((1 + ‖z‖ * |z.im|⁻¹) + |z.im|⁻¹) := by
  set g := ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f
  set u := A.stageResolvent n z hz g
  have hg : ‖g‖ ≤ 1 := (norm_adjoint_isometry_apply_le _ f).trans hf
  have hu : ‖u‖ ≤ |z.im|⁻¹ := by
    calc ‖u‖ ≤ |z.im|⁻¹ * ‖g‖ := A.norm_stageResolvent_apply_le n hz g
      _ ≤ |z.im|⁻¹ * 1 := by gcongr
      _ = |z.im|⁻¹ := mul_one _
  have hDu : ‖A.stage n u‖ ≤ 1 + ‖z‖ * |z.im|⁻¹ := by
    have h : A.stage n u = g + z • u := by
      have := A.stage_stageResolvent n hz g
      rw [← this]
      abel
    rw [h]
    calc ‖g + z • u‖ ≤ ‖g‖ + ‖z • u‖ := norm_add_le _ _
      _ ≤ 1 + ‖z‖ * |z.im|⁻¹ := by
          rw [norm_smul]
          gcongr
  calc A.discreteNorm n u ≤ A.graphConst * (‖A.stage n u‖ + ‖u‖) := A.discreteNorm_le n u
    _ ≤ A.graphConst * ((1 + ‖z‖ * |z.im|⁻¹) + |z.im|⁻¹) := by
        gcongr
        exact A.graphConst_nonneg

/-- **Rellich step.** The compressed resolvents form a collectively compact family. -/
theorem collectivelyCompact_embeddedResolvent {z : ℂ} (hz : z.im ≠ 0) :
    (constantSystem ℂ H).CollectivelyCompact (A.embeddedResolvent z hz) := by
  apply System.collectivelyCompact_of_compact_approximations
  intro ε hε
  set B : ℝ := A.graphConst * ((1 + ‖z‖ * |z.im|⁻¹) + |z.im|⁻¹)
  have hev : ∀ᶠ n in atTop, A.reconstructError n * B < ε := by
    have := A.reconstructError_tendsto.mul_const B
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨K, hK, hKsub⟩ :=
    A.sobolev_compact.image_closedBall_subset_compact (A.reconstructConst * B)
  refine ⟨K ∪ ⋃ n ∈ Set.Iio N,
    ((A.embed n).toContinuousLinearMap ∘L A.stageResolvent n z hz) '' Metric.closedBall 0 1,
    hK.union ((Set.finite_Iio N).isCompact_biUnion fun n _ => ?_), ?_⟩
  · have : ProperSpace (Hn n) := FiniteDimensional.proper_rclike ℂ (Hn n)
    exact (isCompact_closedBall (0 : Hn n) 1).image (map_continuous _)
  · intro y hy
    simp only [System.embeddedUnitBallOutputs, Set.mem_iUnion, Set.mem_image] at hy
    obtain ⟨n, f, hf, rfl⟩ := hy
    have hf' : ‖f‖ ≤ 1 := by simpa using hf
    have hy : (constantSystem ℂ H).embeddedOperator (A.embeddedResolvent z hz) n f =
        A.embed n (A.stageResolvent n z hz
          (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f)) := by
      simp [System.embeddedOperator, constantSystem, embeddedResolvent_apply]
    rw [hy]
    set u := A.stageResolvent n z hz
      (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f)
    by_cases hn : n < N
    · refine ⟨A.embed n u, Or.inr ?_, by simpa using hε⟩
      refine Set.mem_biUnion (show n ∈ Set.Iio N from hn) ?_
      refine ⟨ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f, ?_, rfl⟩
      simpa using (norm_adjoint_isometry_apply_le _ f).trans hf'
    · push Not at hn
      have hB := A.discreteNorm_stageResolvent_le hz n f hf'
      refine ⟨A.sobolev (A.reconstruct n u), Or.inl (hKsub ⟨A.reconstruct n u, ?_, rfl⟩), ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (A.norm_reconstruct_le n u).trans
          (mul_le_mul_of_nonneg_left hB A.reconstructConst_nonneg)
      · rw [dist_eq_norm, norm_sub_rev]
        calc ‖A.sobolev (A.reconstruct n u) - A.embed n u‖
            ≤ A.reconstructError n * A.discreteNorm n u :=
              A.norm_sobolev_reconstruct_sub_embed_le n u
          _ ≤ A.reconstructError n * B :=
              mul_le_mul_of_nonneg_left hB (A.reconstructError_nonneg n)
          _ < ε := hN n hn

/-! ### The norm-resolvent theorem -/

/-- **`thm:supp-compact-spin-resolvent`, `eq:supp-global-norm-resolvent`** (abstract surrogate).
For a compatible stable atlas and every non-real `z`, the compressed resolvents
`W_h (D_h - z)⁻¹ W_h^*` converge in operator norm to `(D̂ - z)⁻¹`, and the limit is compact. -/
theorem isCompactOperator_and_tendsto_embeddedResolvent {z : ℂ} (hz : z.im ≠ 0) :
    IsCompactOperator (A.limit.resolvent z hz) ∧
      Tendsto (A.embeddedResolvent z hz) atTop (𝓝 (A.limit.resolvent z hz)) := by
  apply System.tendsto_operatorNorm_of_collectivelyCompact_of_adjointStrong
  · exact A.collectivelyCompact_embeddedResolvent hz
  · exact A.tendsto_embeddedResolvent_apply hz
  · intro y
    have hz' := SelfAdjointResolventData.conj_im_ne_zero hz
    simp_rw [A.adjoint_embeddedResolvent hz hz', A.limit.adjoint_resolvent hz hz']
    exact A.tendsto_embeddedResolvent_apply hz' y

/-- **`thm:supp-compact-spin-resolvent`**: `‖W_h (D_h - z)⁻¹ W_h^* - (D̂ - z)⁻¹‖ → 0`. -/
theorem tendsto_embeddedResolvent {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (A.embeddedResolvent z hz) atTop (𝓝 (A.limit.resolvent z hz)) :=
  (A.isCompactOperator_and_tendsto_embeddedResolvent hz).2

/-- **`eq:supp-global-norm-resolvent`** in norm form. -/
theorem tendsto_norm_embeddedResolvent_sub {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun n => ‖A.embeddedResolvent z hz n - A.limit.resolvent z hz‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (A.tendsto_embeddedResolvent hz)

/-- The limit resolvent is compact (the abstract Rellich conclusion). -/
theorem isCompactOperator_limit_resolvent {z : ℂ} (hz : z.im ≠ 0) :
    IsCompactOperator (A.limit.resolvent z hz) :=
  (A.isCompactOperator_and_tendsto_embeddedResolvent hz).1

/-- **`thm:compact-spin-main`, spin clause `eq:compact-spin-resolvent-main`** (abstract
surrogate): once the finite covariant Wilson operators form a compatible stable atlas, the
compressed resolvents converge in norm to the resolvent of the doubled Dirac operator for every
non-real `z`. -/
theorem compactSpinMain_norm_resolvent (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun n => ‖A.embeddedResolvent z hz n - A.limit.resolvent z hz‖) atTop (𝓝 0) :=
  A.tendsto_norm_embeddedResolvent_sub hz

/-! ### Spectral projections -/

/-- **Spectral-projection clause of `thm:supp-compact-spin-resolvent`**, in resolvent form:
for every circle in the resolvent set of the limit resolvent `(D̂ - z)⁻¹` (an isolated spectral
cluster of `D̂` after the Möbius map `λ ↦ (λ - z)⁻¹`), the Riesz projections of the compressed
resolvents converge in operator norm to the Riesz projection of `(D̂ - z)⁻¹`. -/
theorem circleRieszProjection_embeddedResolvent_tendsto {z : ℂ} (hz : z.im ≠ 0)
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hunit : ∀ w ∈ Metric.sphere center radius, w ∈ resolventSet ℂ (A.limit.resolvent z hz)) :
    Tendsto (fun n => ResolventStability.circleRieszProjection
        (A.embeddedResolvent z hz n) center radius) atTop
      (𝓝 (ResolventStability.circleRieszProjection (A.limit.resolvent z hz) center radius)) := by
  obtain ⟨M, hM, hbound⟩ :=
    ResolventStability.exists_circle_resolvent_norm_bound (A.limit.resolvent z hz) center radius
      hunit
  obtain ⟨N, -, hN⟩ := ResolventStability.eventually_circle_resolvent_bound_of_tendsto
    (A.embeddedResolvent z hz) (A.limit.resolvent z hz) (A.tendsto_embeddedResolvent hz)
    center radius M hM hunit hbound
  refine ResolventStability.circleRieszProjection_tendsto (A.tendsto_embeddedResolvent hz)
    center radius hradius M N hM hunit hbound ?_ ?_
  · filter_upwards [hN] with n hn
    exact fun w hw => (hn w hw).1
  · filter_upwards [hN] with n hn
    exact fun w hw => (hn w hw).2

end CompatibleStableAtlas

end RenewalGeometry
