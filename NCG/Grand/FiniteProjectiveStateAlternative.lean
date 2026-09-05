/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProjectiveStateAlternative
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Finite C-star projective state alternative

This supplies the C-star-specific content of
`thm:projective-state-alternative`: compact finite-stage state spaces, the
closed inverse-limit compatibility equations, coordinatewise characterization
of a singleton cluster set, and a self-adjoint finite-stage separator realized
along two cofinal subsequences.
-/

open Filter Topology
open scoped ComplexStarModule

namespace NCG

noncomputable section

/-- Closed defining conditions for a state on a finite-dimensional unital
complex C-star algebra.  Positivity is recorded on every `x⋆x`; star
preservation is retained explicitly because it is used by the finite
self-adjoint separator. -/
def FiniteCStarStateData (A : Type*) [CStarAlgebra A]
    (φ : A →L[ℂ] ℂ) : Prop :=
  ‖φ‖ ≤ 1 ∧ φ 1 = 1 ∧
    (∀ x : A, 0 ≤ (φ (star x * x)).re) ∧
    ∀ x : A, φ (star x) = star (φ x)

/-- The finite-stage C-star state space. -/
abbrev FiniteCStarState (A : Type*) [CStarAlgebra A] :=
  {φ : A →L[ℂ] ℂ // FiniteCStarStateData A φ}

instance (A : Type*) [CStarAlgebra A] : CoeFun (FiniteCStarState A)
    (fun _ => A → ℂ) := ⟨fun φ => φ.1⟩

/-- Evaluation at one algebra element is continuous on the finite-stage state
space. -/
theorem continuous_finiteCStarState_apply
    {A : Type*} [CStarAlgebra A] [FiniteDimensional ℂ A] (x : A) :
    Continuous (fun φ : FiniteCStarState A => φ x) := by
  exact ((ContinuousLinearMap.apply ℂ ℂ x).continuous).comp continuous_subtype_val

/-- The defining finite-stage state conditions form a closed subset of the
continuous dual. -/
theorem isClosed_finiteCStarStateData
    (A : Type*) [CStarAlgebra A] [FiniteDimensional ℂ A] :
    IsClosed {φ : A →L[ℂ] ℂ | FiniteCStarStateData A φ} := by
  let ev : A → (A →L[ℂ] ℂ) → ℂ := fun x φ => φ x
  have hev (x : A) : Continuous (ev x) :=
    (ContinuousLinearMap.apply ℂ ℂ x).continuous
  have hnorm : IsClosed {φ : A →L[ℂ] ℂ | ‖φ‖ ≤ 1} :=
    isClosed_Iic.preimage continuous_norm
  have hone : IsClosed {φ : A →L[ℂ] ℂ | φ 1 = 1} :=
    isClosed_eq (hev 1) continuous_const
  have hpos : IsClosed {φ : A →L[ℂ] ℂ |
      ∀ x : A, 0 ≤ (φ (star x * x)).re} := by
    rw [show {φ : A →L[ℂ] ℂ | ∀ x : A, 0 ≤ (φ (star x * x)).re} =
        ⋂ x : A, {φ : A →L[ℂ] ℂ | 0 ≤ (φ (star x * x)).re} by
      ext φ
      simp]
    exact isClosed_iInter fun x =>
      isClosed_le continuous_const (Complex.continuous_re.comp (hev (star x * x)))
  have hstar : IsClosed {φ : A →L[ℂ] ℂ |
      ∀ x : A, φ (star x) = star (φ x)} := by
    rw [show {φ : A →L[ℂ] ℂ | ∀ x : A, φ (star x) = star (φ x)} =
        ⋂ x : A, {φ : A →L[ℂ] ℂ | φ (star x) = star (φ x)} by
      ext φ
      simp]
    exact isClosed_iInter fun x =>
      isClosed_eq (hev (star x)) ((hev x).star)
  unfold FiniteCStarStateData
  exact hnorm.inter (hone.inter (hpos.inter hstar))

/-- A finite-dimensional C-star state space is compact in the norm topology
of the dual. -/
theorem isCompact_finiteCStarStateData
    (A : Type*) [CStarAlgebra A] [FiniteDimensional ℂ A] :
    IsCompact {φ : A →L[ℂ] ℂ | FiniteCStarStateData A φ} := by
  letI : ProperSpace (A →L[ℂ] ℂ) := FiniteDimensional.proper ℂ (A →L[ℂ] ℂ)
  refine (isCompact_closedBall (0 : A →L[ℂ] ℂ) 1).of_isClosed_subset
    (isClosed_finiteCStarStateData A) ?_
  intro φ hφ
  simpa [Metric.mem_closedBall, dist_zero_right] using hφ.1

noncomputable instance finiteCStarState_compactSpace
    (A : Type*) [CStarAlgebra A] [FiniteDimensional ℂ A] :
    CompactSpace (FiniteCStarState A) :=
  isCompact_iff_compactSpace.mp (isCompact_finiteCStarStateData A)

/-- Product of all finite-stage state spaces. -/
abbrev ProjectiveFiniteStateSpace
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)] :=
  ∀ n, FiniteCStarState (A n)

/-- Adjacent inverse-limit compatibility for a family of finite-stage states. -/
def ProjectiveStateCompatible
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    (ι : ∀ n, A n →L[ℂ] A (n + 1))
    (Ω : ProjectiveFiniteStateSpace A) : Prop :=
  ∀ n x, Ω (n + 1) (ι n x) = Ω n x

/-- The inverse-limit compatibility equations are closed in the Tychonoff
product. -/
theorem isClosed_projectiveStateCompatible
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    [∀ n, FiniteDimensional ℂ (A n)]
    (ι : ∀ n, A n →L[ℂ] A (n + 1)) :
    IsClosed {Ω : ProjectiveFiniteStateSpace A |
      ProjectiveStateCompatible A ι Ω} := by
  rw [show {Ω : ProjectiveFiniteStateSpace A |
        ProjectiveStateCompatible A ι Ω} =
      ⋂ n : ℕ, ⋂ x : A n,
        {Ω : ProjectiveFiniteStateSpace A |
          Ω (n + 1) (ι n x) = Ω n x} by
    ext Ω
    simp [ProjectiveStateCompatible]]
  exact isClosed_iInter fun n => isClosed_iInter fun x =>
    isClosed_eq
      ((continuous_finiteCStarState_apply (ι n x)).comp (continuous_apply (n + 1)))
      ((continuous_finiteCStarState_apply x).comp (continuous_apply n))

/-- Projective cluster states: cluster points of all finite restrictions which
satisfy the closed inverse-limit equations. -/
def ProjectiveCStarClusterSet
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    (ι : ∀ n, A n →L[ℂ] A (n + 1))
    (u : ℕ → ProjectiveFiniteStateSpace A) :
    Set (ProjectiveFiniteStateSpace A) :=
  {Ω | MapClusterPt Ω atTop u ∧ ProjectiveStateCompatible A ι Ω}

/-- Eventual finite-stage compatibility forces every projective cluster point
to obey the exact adjacent inverse-limit equations. -/
theorem mapClusterPt_projectiveStateCompatible
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    [∀ n, FiniteDimensional ℂ (A n)]
    (ι : ∀ n, A n →L[ℂ] A (n + 1))
    (u : ℕ → ProjectiveFiniteStateSpace A)
    (hevent : ∀ n x, ∀ᶠ k in atTop,
      u k (n + 1) (ι n x) = u k n x)
    {Ω : ProjectiveFiniteStateSpace A} (hΩ : MapClusterPt Ω atTop u) :
    ProjectiveStateCompatible A ι Ω := by
  intro n x
  let S : Set (ProjectiveFiniteStateSpace A) :=
    {Ξ | Ξ (n + 1) (ι n x) = Ξ n x}
  have hS : IsClosed S := isClosed_eq
    ((continuous_finiteCStarState_apply (ι n x)).comp (continuous_apply (n + 1)))
    ((continuous_finiteCStarState_apply x).comp (continuous_apply n))
  exact hS.mem_of_mapClusterPt hΩ (hevent n x)

/-- Under eventual adjacent compatibility, the projective cluster set is
exactly the ordinary cluster set in the compact product. -/
theorem projectiveCStarClusterSet_eq_clusterSet
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    [∀ n, FiniteDimensional ℂ (A n)]
    (ι : ∀ n, A n →L[ℂ] A (n + 1))
    (u : ℕ → ProjectiveFiniteStateSpace A)
    (hevent : ∀ n x, ∀ᶠ k in atTop,
      u k (n + 1) (ι n x) = u k n x) :
    ProjectiveCStarClusterSet A ι u =
      {Ω | MapClusterPt Ω atTop u} := by
  ext Ω
  constructor
  · exact fun h => h.1
  · intro hΩ
    exact ⟨hΩ, mapClusterPt_projectiveStateCompatible A ι u hevent hΩ⟩

/-- Tychonoff compactness and closed compatibility give a nonempty compact
inverse-limit cluster set. -/
theorem projectiveCStarClusterSet_nonempty_compact
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    [∀ n, FiniteDimensional ℂ (A n)]
    (ι : ∀ n, A n →L[ℂ] A (n + 1))
    (u : ℕ → ProjectiveFiniteStateSpace A)
    (hevent : ∀ n x, ∀ᶠ k in atTop,
      u k (n + 1) (ι n x) = u k n x) :
    (ProjectiveCStarClusterSet A ι u).Nonempty ∧
      IsCompact (ProjectiveCStarClusterSet A ι u) := by
  have hgeneric := projective_state_alternative u
  rw [projectiveCStarClusterSet_eq_clusterSet A ι u hevent]
  exact ⟨hgeneric.1, hgeneric.2.2.1⟩

/-- A projective cluster set is a singleton exactly when every expectation of
every fixed finite-stage observable converges. -/
theorem projectiveCStarClusterSet_singleton_iff_coordinate_converges
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    [∀ n, FiniteDimensional ℂ (A n)]
    (ι : ∀ n, A n →L[ℂ] A (n + 1))
    (u : ℕ → ProjectiveFiniteStateSpace A)
    (hevent : ∀ n x, ∀ᶠ k in atTop,
      u k (n + 1) (ι n x) = u k n x) :
    (∃ Ω, ProjectiveCStarClusterSet A ι u = {Ω}) ↔
      ∀ m x, ∃ z : ℂ,
        Tendsto (fun n => u n m x) atTop (nhds z) := by
  constructor
  · rintro ⟨Ω, hsingleton⟩
    have hunique : ∀ Ξ, MapClusterPt Ξ atTop u → Ξ = Ω := by
      intro Ξ hΞ
      have hmem : Ξ ∈ ProjectiveCStarClusterSet A ι u :=
        ⟨hΞ, mapClusterPt_projectiveStateCompatible A ι u hevent hΞ⟩
      rw [hsingleton] at hmem
      exact hmem
    have hu : Tendsto u atTop (nhds Ω) :=
      tendsto_nhds_of_unique_mapClusterPt hunique
    intro m x
    refine ⟨Ω m x, ?_⟩
    exact (((continuous_finiteCStarState_apply x).comp
      (continuous_apply m)).tendsto Ω).comp hu
  · intro hcoord
    obtain ⟨Ω, hΩ⟩ :=
      (projectiveCStarClusterSet_nonempty_compact A ι u hevent).1
    refine ⟨Ω, Set.eq_singleton_iff_unique_mem.mpr ⟨hΩ, ?_⟩⟩
    intro Ξ hΞ
    apply funext
    intro m
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    obtain ⟨z, hz⟩ := hcoord m x
    have hcΞ : MapClusterPt (Ξ m x) atTop (fun n => u n m x) := by
      simpa [Function.comp_def] using hΞ.1.continuousAt_comp
        (((continuous_finiteCStarState_apply x).comp
          (continuous_apply m)).continuousAt)
    obtain ⟨σ, hσ, hlimΞ⟩ := hcΞ.tendsto_subseq
    have hlimz : Tendsto ((fun n => u n m x) ∘ σ) atTop (nhds z) :=
      hz.comp hσ.tendsto_atTop
    have hΞz : Ξ m x = z := tendsto_nhds_unique hlimΞ hlimz
    have hcΩ : MapClusterPt (Ω m x) atTop (fun n => u n m x) := by
      simpa [Function.comp_def] using hΩ.1.continuousAt_comp
        (((continuous_finiteCStarState_apply x).comp
          (continuous_apply m)).continuousAt)
    obtain ⟨τ, hτ, hlimΩ⟩ := hcΩ.tendsto_subseq
    have hlimz' : Tendsto ((fun n => u n m x) ∘ τ) atTop (nhds z) :=
      hz.comp hτ.tendsto_atTop
    exact hΞz.trans (tendsto_nhds_unique hlimΩ hlimz').symm

/-- Two unequal complex-linear states differ on a self-adjoint observable:
decompose any separating element into its real and imaginary self-adjoint
parts. -/
theorem finiteCStarState_exists_selfAdjoint_separator
    {A : Type*} [CStarAlgebra A]
    {φ ψ : FiniteCStarState A} (hne : φ ≠ ψ) :
    ∃ a : A, IsSelfAdjoint a ∧ φ a ≠ ψ a := by
  have hmaps : (φ.1 : A →L[ℂ] ℂ) ≠ ψ.1 := by
    intro h
    exact hne (Subtype.ext h)
  have happ : ∃ x : A, φ x ≠ ψ x := by
    by_contra h
    push Not at h
    exact hmaps (ContinuousLinearMap.ext h)
  obtain ⟨x, hx⟩ := happ
  by_cases hr : φ (ℜ x : A) ≠ ψ (ℜ x : A)
  · exact ⟨(ℜ x : A), (ℜ x).property, hr⟩
  by_cases hi : φ (ℑ x : A) ≠ ψ (ℑ x : A)
  · exact ⟨(ℑ x : A), (ℑ x).property, hi⟩
  exfalso
  apply hx
  rw [← realPart_add_I_smul_imaginaryPart x]
  simp only [map_add, map_smul]
  rw [not_ne_iff.mp hr, not_ne_iff.mp hi]

/-- Distinct compatible cluster states are separated on one finite stage by a
self-adjoint observable, with a positive margin, and both values are realized
as limits along cofinal subsequences. -/
theorem projectiveCStarClusterSet_finite_selfAdjoint_separator
    (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    [∀ n, FiniteDimensional ℂ (A n)]
    (ι : ∀ n, A n →L[ℂ] A (n + 1))
    (u : ℕ → ProjectiveFiniteStateSpace A)
    {Ω₁ Ω₂ : ProjectiveFiniteStateSpace A}
    (hΩ₁ : Ω₁ ∈ ProjectiveCStarClusterSet A ι u)
    (hΩ₂ : Ω₂ ∈ ProjectiveCStarClusterSet A ι u)
    (hne : Ω₁ ≠ Ω₂) :
    ∃ m : ℕ, ∃ a : A m, ∃ ε : ℝ, ∃ σ₁ σ₂ : ℕ → ℕ,
      IsSelfAdjoint a ∧ 0 < ε ∧ StrictMono σ₁ ∧ StrictMono σ₂ ∧
      Tendsto (fun k => u (σ₁ k) m a) atTop (nhds (Ω₁ m a)) ∧
      Tendsto (fun k => u (σ₂ k) m a) atTop (nhds (Ω₂ m a)) ∧
      ε ≤ dist (Ω₁ m a) (Ω₂ m a) := by
  have hexm : ∃ m, Ω₁ m ≠ Ω₂ m := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨m, hm⟩ := hexm
  obtain ⟨a, ha, hsep⟩ :=
    finiteCStarState_exists_selfAdjoint_separator hm
  obtain ⟨σ₁, hσ₁, hlim₁⟩ := hΩ₁.1.tendsto_subseq
  obtain ⟨σ₂, hσ₂, hlim₂⟩ := hΩ₂.1.tendsto_subseq
  have heval : Continuous (fun Ω : ProjectiveFiniteStateSpace A => Ω m a) :=
    (continuous_finiteCStarState_apply a).comp (continuous_apply m)
  have hev₁ : Tendsto (fun k => u (σ₁ k) m a) atTop (nhds (Ω₁ m a)) := by
    simpa [Function.comp_def] using (heval.tendsto Ω₁).comp hlim₁
  have hev₂ : Tendsto (fun k => u (σ₂ k) m a) atTop (nhds (Ω₂ m a)) := by
    simpa [Function.comp_def] using (heval.tendsto Ω₂).comp hlim₂
  let ε := dist (Ω₁ m a) (Ω₂ m a) / 2
  have hdist : 0 < dist (Ω₁ m a) (Ω₂ m a) := dist_pos.mpr hsep
  refine ⟨m, a, ε, σ₁, σ₂, ha, half_pos hdist, hσ₁, hσ₂,
    hev₁, hev₂, ?_⟩
  dsimp [ε]
  linarith

end

end NCG
