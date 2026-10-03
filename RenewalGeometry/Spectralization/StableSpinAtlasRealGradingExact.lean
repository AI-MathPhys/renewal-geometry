/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.CompatibleStableAtlasNormResolvent

/-!
# Real and grading structures on a compatible stable spin discretization

Paper `predictive_spectral_geometry`, label `def:stable-spin-atlas`, the optional last clause of
(A3): "When real and grading structures are asserted, their finite actions intertwine these
reconstructions and converge to the declared continuum actions."

`CompatibleStableAtlas` (in `OperatorLimits/CompatibleStableAtlasNormResolvent.lean`) encodes
(A1)–(A3).  This file adds the asserted real/grading structure.

* `StableSpinAtlasRealGrading.ContinuumRealGrading`: the *declared* continuum actions on
  `ℋ = L²(M; S ⊗ ℂ²)` — an antiunitary `J` (`ℋ ≃ₗᵢ⋆[ℂ] ℋ`) with `J² = ε`, and a self-adjoint
  involutive grading `γ`, with `J D̂ = ε' D̂ J`, `γ D̂ = -D̂ γ` on the domain of `D̂` (which both
  preserve) and `J γ = ε'' γ J`, together with their actions `J_V`, `γ_V` on the first-order
  space `V = H¹` intertwined by the Sobolev embedding.
* `StableSpinAtlasRealGrading.AtlasRealGrading A`: for a compatible stable atlas `A`, the finite
  actions — antiunitaries `J_h` and gradings `γ_h` on `ℋ_h` with `J_h D_h = ε' D_h J_h` and
  `γ_h D_h = -D_h γ_h` — intertwining the reconstructions: `W_h J_h = J W_h`,
  `W_h γ_h = γ W_h`, `I_h J_h = J_V I_h`, `I_h γ_h = γ_V I_h`.

Derived (not assumed):

* `tendsto_embed_stageReal_adjoint`, `tendsto_embed_stageGrading_adjoint` — the convergence
  clause: `W_h J_h W_h^* f → J f` and `W_h γ_h W_h^* f → γ f` for every `f`, from the
  intertwining and (A1) `W_h W_h^* → I`;
* `stageReal_sq`, `stageGrading_sq`, `stageReal_stageGrading`, `stageGrading_eq_compress`,
  `isSelfAdjoint_stageGrading` — the finite actions inherit the declared signs `J_h² = ε`,
  `γ_h² = 1`, `J_h γ_h = ε'' γ_h J_h` and `γ_h = W_h^* γ W_h` is self-adjoint, because `W_h` is
  an isometry.

Non-vacuity: `exampleAtlas` / `exampleRealGrading` — the doubled one-point model
`ℋ = ℂ²`, `D̂ = σ₁`, `γ = σ₃`, `J` = complex conjugation, with all stages equal to the limit.
-/

open Filter Topology ComplexConjugate
open scoped InnerProductSpace

noncomputable section

namespace RenewalGeometry

namespace StableSpinAtlasRealGrading

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]

/-- A sign `±1`. -/
def IsSign (s : ℝ) : Prop := s = 1 ∨ s = -1

/-- **Declared continuum real and grading structures** (`def:stable-spin-atlas`).  For the
self-adjoint operator `T` (the surrogate of `D̂ = D_{M,𝔰} ⊗ σ₁`) and the first-order space `V`
with embedding `sobolev : V → ℋ`: an antiunitary `J` with `J² = ε`, a self-adjoint involution
`γ`, both preserving the domain, with `J T = ε' T J`, `γ T = -T γ`, `J γ = ε'' γ J`, and actions
`J_V`, `γ_V` on `V` intertwined by `sobolev`. -/
structure ContinuumRealGrading (T : SelfAdjointResolventData H) (sobolev : V →L[ℂ] H) where
  /-- The real structure `J` (antiunitary). -/
  realJ : H ≃ₗᵢ⋆[ℂ] H
  /-- `ε`: `J² = ε`. -/
  realSign : ℝ
  realSign_isSign : IsSign realSign
  realJ_realJ : ∀ f, realJ (realJ f) = (realSign : ℂ) • f
  /-- `ε'`: `J D̂ = ε' D̂ J`. -/
  diracSign : ℝ
  diracSign_isSign : IsSign diracSign
  realJ_mem_domain : ∀ u ∈ T.op.domain, realJ u ∈ T.op.domain
  op_realJ : ∀ u : T.op.domain,
    T.op ⟨realJ u, realJ_mem_domain u u.2⟩ = (diracSign : ℂ) • realJ (T.op u)
  /-- The grading `γ`. -/
  grading : H →L[ℂ] H
  isSelfAdjoint_grading : IsSelfAdjoint grading
  grading_grading : ∀ f, grading (grading f) = f
  grading_mem_domain : ∀ u ∈ T.op.domain, grading u ∈ T.op.domain
  op_grading : ∀ u : T.op.domain,
    T.op ⟨grading u, grading_mem_domain u u.2⟩ = -grading (T.op u)
  /-- `ε''`: `J γ = ε'' γ J`. -/
  gradingSign : ℝ
  gradingSign_isSign : IsSign gradingSign
  realJ_grading : ∀ f, realJ (grading f) = (gradingSign : ℂ) • grading (realJ f)
  /-- The actions on the first-order space `V = H¹`. -/
  realJV : V →ₗ⋆[ℂ] V
  gradingV : V →ₗ[ℂ] V
  sobolev_realJV : ∀ x, sobolev (realJV x) = realJ (sobolev x)
  sobolev_gradingV : ∀ x, sobolev (gradingV x) = grading (sobolev x)

/-- **The asserted real/grading clause of `def:stable-spin-atlas`.**  For a compatible stable
atlas `A`: declared continuum actions `toContinuumRealGrading`, finite antiunitaries `J_h` and
gradings `γ_h` with `J_h D_h = ε' D_h J_h` and `γ_h D_h = -D_h γ_h`, intertwining the
reconstructions `W_h` and `I_h`.  The convergence to the continuum actions is *derived*
(`tendsto_embed_stageReal_adjoint`, `tendsto_embed_stageGrading_adjoint`). -/
structure AtlasRealGrading (A : CompatibleStableAtlas H V Hn) extends
    ContinuumRealGrading A.limit A.sobolev where
  /-- The finite real structures `J_h`. -/
  stageReal : ∀ n, Hn n ≃ₗᵢ⋆[ℂ] Hn n
  /-- The finite gradings `γ_h`. -/
  stageGrading : ∀ n, Hn n →L[ℂ] Hn n
  stage_stageReal : ∀ n u, A.stage n (stageReal n u) = (diracSign : ℂ) • stageReal n (A.stage n u)
  stage_stageGrading : ∀ n u, A.stage n (stageGrading n u) = -stageGrading n (A.stage n u)
  /-- `W_h J_h = J W_h`. -/
  embed_stageReal : ∀ n u, A.embed n (stageReal n u) = realJ (A.embed n u)
  /-- `W_h γ_h = γ W_h`. -/
  embed_stageGrading : ∀ n u, A.embed n (stageGrading n u) = grading (A.embed n u)
  /-- `I_h J_h = J_V I_h`. -/
  reconstruct_stageReal : ∀ n u, A.reconstruct n (stageReal n u) = realJV (A.reconstruct n u)
  /-- `I_h γ_h = γ_V I_h`. -/
  reconstruct_stageGrading : ∀ n u,
    A.reconstruct n (stageGrading n u) = gradingV (A.reconstruct n u)

namespace AtlasRealGrading

variable {A : CompatibleStableAtlas H V Hn} (S : AtlasRealGrading A)

/-- **Convergence of the finite real structures** (`def:stable-spin-atlas`, derived):
`W_h J_h W_h^* f → J f` for every `f ∈ ℋ`. -/
theorem tendsto_embed_stageReal_adjoint (f : H) :
    Tendsto (fun n => A.embed n (S.stageReal n
      (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f))) atTop
      (𝓝 (S.realJ f)) := by
  have h := (S.realJ.continuous.tendsto f).comp (A.embed_adjoint_tendsto f)
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, S.embed_stageReal]

/-- **Convergence of the finite gradings** (`def:stable-spin-atlas`, derived):
`W_h γ_h W_h^* f → γ f` for every `f ∈ ℋ`. -/
theorem tendsto_embed_stageGrading_adjoint (f : H) :
    Tendsto (fun n => A.embed n (S.stageGrading n
      (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f))) atTop
      (𝓝 (S.grading f)) := by
  have h := (S.grading.continuous.tendsto f).comp (A.embed_adjoint_tendsto f)
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, S.embed_stageGrading]

/-- `W_h` is injective. -/
theorem embed_injective (n : ℕ) : Function.Injective (A.embed n) :=
  (A.embed n).injective

/-- The finite real structures inherit `J_h² = ε`. -/
theorem stageReal_sq (n : ℕ) (u : Hn n) :
    S.stageReal n (S.stageReal n u) = (S.realSign : ℂ) • u := by
  apply (A.embed n).injective
  rw [S.embed_stageReal, S.embed_stageReal, S.realJ_realJ, LinearIsometry.map_smul]

/-- The finite gradings inherit `γ_h² = 1`. -/
theorem stageGrading_sq (n : ℕ) (u : Hn n) : S.stageGrading n (S.stageGrading n u) = u := by
  apply (A.embed n).injective
  rw [S.embed_stageGrading, S.embed_stageGrading, S.grading_grading]

/-- The finite actions inherit `J_h γ_h = ε'' γ_h J_h`. -/
theorem stageReal_stageGrading (n : ℕ) (u : Hn n) :
    S.stageReal n (S.stageGrading n u) = (S.gradingSign : ℂ) • S.stageGrading n (S.stageReal n u) := by
  apply (A.embed n).injective
  rw [S.embed_stageReal, S.embed_stageGrading, S.realJ_grading, LinearIsometry.map_smul,
    S.embed_stageGrading, S.embed_stageReal]

/-- `γ_h = W_h^* γ W_h`. -/
theorem stageGrading_eq_compress (n : ℕ) :
    S.stageGrading n = ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap ∘L
      S.grading ∘L (A.embed n).toContinuousLinearMap := by
  ext u
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [← S.embed_stageGrading, adjoint_isometry_apply_map]

/-- The finite gradings are self-adjoint. -/
theorem isSelfAdjoint_stageGrading (n : ℕ) : IsSelfAdjoint (S.stageGrading n) := by
  rw [S.stageGrading_eq_compress n]
  have hγ := S.isSelfAdjoint_grading
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint S.grading, hγ.star_eq, ContinuousLinearMap.comp_assoc]

end AtlasRealGrading

/-! ### Non-vacuity: the doubled one-point model -/

section nonvacuity

/-- `ℂ²`. -/
abbrev C2 := EuclideanSpace ℂ (Fin 2)

/-- The Pauli matrix `σ₁`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `σ₃`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauliX_isSelfAdjoint : IsSelfAdjoint pauliX := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX]

theorem pauliZ_isSelfAdjoint : IsSelfAdjoint pauliZ := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ]

/-- `σ₁` as an operator on `ℂ²`. -/
def opX : C2 →L[ℂ] C2 := Matrix.toEuclideanCLM (𝕜 := ℂ) pauliX

/-- `σ₃` as an operator on `ℂ²`. -/
def opZ : C2 →L[ℂ] C2 := Matrix.toEuclideanCLM (𝕜 := ℂ) pauliZ

theorem opX_isSelfAdjoint : IsSelfAdjoint opX := pauliX_isSelfAdjoint.map _

theorem opZ_isSelfAdjoint : IsSelfAdjoint opZ := pauliZ_isSelfAdjoint.map _

theorem opX_apply (x : C2) : opX x = WithLp.toLp 2 ![x 1, x 0] := by
  ext i
  fin_cases i <;> simp [opX, pauliX, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem opZ_apply (x : C2) : opZ x = WithLp.toLp 2 ![x 0, -x 1] := by
  ext i
  fin_cases i <;> simp [opZ, pauliZ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Componentwise complex conjugation on `ℂ²`, an antiunitary involution. -/
def conjC2 : C2 ≃ₗᵢ⋆[ℂ] C2 where
  toFun x := WithLp.toLp 2 (fun i => star (x i))
  invFun x := WithLp.toLp 2 (fun i => star (x i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  norm_map' x := by simp [EuclideanSpace.norm_eq]

@[simp] theorem conjC2_apply (x : C2) (i : Fin 2) : conjC2 x i = star (x i) := rfl

/-- The one-point doubled model as a compatible stable atlas: `ℋ = ℋ_h = V = ℂ²`,
`D̂ = D_h = σ₁`, `W_h = I_h = id`. -/
def exampleAtlas : CompatibleStableAtlas C2 C2 (fun _ => C2) where
  limit := SelfAdjointResolventData.ofBounded opX opX_isSelfAdjoint
  core := ⊤
  core_le := le_top
  core_dense u := ⟨fun _ => u, fun _ => Submodule.mem_top, tendsto_const_nhds, tendsto_const_nhds⟩
  sobolev := ContinuousLinearMap.id ℂ C2
  sobolev_compact := (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).mpr inferInstance
  embed _ := LinearIsometry.id
  stage _ := opX
  stage_selfAdjoint _ := opX_isSelfAdjoint
  embed_adjoint_tendsto f := by
    have : ContinuousLinearMap.adjoint (LinearIsometry.id : C2 →ₗᵢ[ℂ] C2).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ C2 := by
      rw [show (LinearIsometry.id : C2 →ₗᵢ[ℂ] C2).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ C2 from rfl]
      exact ContinuousLinearMap.adjoint_id
    simp only [this]
    exact tendsto_const_nhds
  discreteNorm _ u := ‖u‖
  discreteNorm_nonneg _ u := norm_nonneg u
  reconstruct _ := LinearMap.id
  reconstructConst := 1
  reconstructConst_nonneg := zero_le_one
  norm_reconstruct_le _ u := by simp
  reconstructError _ := 0
  reconstructError_nonneg _ := le_rfl
  reconstructError_tendsto := tendsto_const_nhds
  norm_sobolev_reconstruct_sub_embed_le _ u := by simp
  graphConst := 1
  graphConst_nonneg := zero_le_one
  discreteNorm_le _ u := by
    simp only [one_mul]
    exact le_add_of_nonneg_left (norm_nonneg _)
  sample _ ψ := ψ
  embed_sample_tendsto ψ := tendsto_const_nhds
  embed_stage_sample_tendsto ψ := tendsto_const_nhds

theorem opX_conjC2 (x : C2) : opX (conjC2 x) = conjC2 (opX x) := by
  ext i; fin_cases i <;> simp [opX_apply]

theorem opZ_conjC2 (x : C2) : opZ (conjC2 x) = conjC2 (opZ x) := by
  ext i; fin_cases i <;> simp [opZ_apply]

theorem opX_opZ (x : C2) : opX (opZ x) = -opZ (opX x) := by
  ext i; fin_cases i <;> simp [opX_apply, opZ_apply]

theorem opZ_opZ (x : C2) : opZ (opZ x) = x := by
  ext i; fin_cases i <;> simp [opZ_apply]

theorem conjC2_conjC2 (x : C2) : conjC2 (conjC2 x) = x := by
  ext i; simp

/-- **Non-vacuity of `AtlasRealGrading`.** The one-point doubled model carries the real
structure `J` = complex conjugation (`ε = ε' = ε'' = 1`) and the grading `γ = σ₃`, which
anticommutes with `D̂ = σ₁`. -/
def exampleRealGrading : AtlasRealGrading exampleAtlas where
  realJ := conjC2
  realSign := 1
  realSign_isSign := Or.inl rfl
  realJ_realJ f := by simp [conjC2_conjC2]
  diracSign := 1
  diracSign_isSign := Or.inl rfl
  realJ_mem_domain _ _ := Submodule.mem_top
  op_realJ u := by
    simp only [Complex.ofReal_one, one_smul]
    exact opX_conjC2 (u : C2)
  grading := opZ
  isSelfAdjoint_grading := opZ_isSelfAdjoint
  grading_grading := opZ_opZ
  grading_mem_domain _ _ := Submodule.mem_top
  op_grading u := opX_opZ (u : C2)
  gradingSign := 1
  gradingSign_isSign := Or.inl rfl
  realJ_grading f := by
    simp only [Complex.ofReal_one, one_smul]
    exact (opZ_conjC2 f).symm
  realJV := conjC2.toLinearIsometry.toLinearMap
  gradingV := opZ.toLinearMap
  sobolev_realJV _ := rfl
  sobolev_gradingV _ := rfl
  stageReal _ := conjC2
  stageGrading _ := opZ
  stage_stageReal _ u := by
    simp only [Complex.ofReal_one, one_smul]
    exact opX_conjC2 (u : C2)
  stage_stageGrading _ u := opX_opZ (u : C2)
  embed_stageReal _ _ := rfl
  embed_stageGrading _ _ := rfl
  reconstruct_stageReal _ _ := rfl
  reconstruct_stageGrading _ _ := rfl

end nonvacuity

end StableSpinAtlasRealGrading

end RenewalGeometry
