/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HankelMinimality
import NCG.Grand.FeedbackRealization
import NCG.Grand.PassiveRealizationSimilarity

/-!
# Canonical realization of a finite-rank operator Hankel kernel

The state carrier is the span of the infinite block-Hankel columns themselves.
Future-index shift preserves this span and is the canonical transition.  The
zero-delay columns give the source and zero-delay evaluation gives the output.
This is the constructive Ho--Kalman converse for operator-valued kernels.
-/

open Matrix Finset

namespace NCG

variable {out inp : Type*} [Fintype out] [Fintype inp]
  [DecidableEq out] [DecidableEq inp]

/-- Scalarized infinite block-Hankel table of an operator kernel. -/
def operatorHankelTable (K : ℕ → Matrix out inp ℂ)
    (f : ℕ × out) (p : ℕ × inp) : ℂ :=
  K (f.1 + p.1) f.2 p.2

/-- One infinite block-Hankel column. -/
def operatorHankelColumn (K : ℕ → Matrix out inp ℂ)
    (p : ℕ × inp) : (ℕ × out) → ℂ :=
  fun f => operatorHankelTable K f p

/-- The canonical finite-memory state space: the span of all Hankel columns. -/
abbrev OperatorHankelSpace (K : ℕ → Matrix out inp ℂ) :=
  HankelCore (ℕ × inp) (ℕ × out) (operatorHankelTable K)

/-- Shift of the future row index on the ambient response space. -/
def hankelFutureShift : ((ℕ × out) → ℂ) →ₗ[ℂ] ((ℕ × out) → ℂ) where
  toFun v f := v (f.1 + 1, f.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Future shift sends a Hankel column to the next past-delay column. -/
theorem hankelFutureShift_column (K : ℕ → Matrix out inp ℂ)
    (p : ℕ × inp) :
    hankelFutureShift (operatorHankelColumn K p) =
      operatorHankelColumn K (p.1 + 1, p.2) := by
  funext f
  simp only [hankelFutureShift, operatorHankelColumn,
    operatorHankelTable, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Nat.add_assoc, Nat.add_comm 1 p.1, ← Nat.add_assoc]

/-- The canonical Hankel transition, obtained by restricting future shift to
the column span. -/
noncomputable def operatorHankelTransition (K : ℕ → Matrix out inp ℂ) :
    OperatorHankelSpace K →ₗ[ℂ] OperatorHankelSpace K :=
  (hankelFutureShift.domRestrict (OperatorHankelSpace K)).codRestrict
    (OperatorHankelSpace K) (by
      intro v
      have hshift : ∀ y : (ℕ × out) → ℂ,
          y ∈ OperatorHankelSpace K →
          hankelFutureShift y ∈ OperatorHankelSpace K := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
            obtain ⟨p, rfl⟩ := hy
            change hankelFutureShift (operatorHankelColumn K p) ∈
              OperatorHankelSpace K
            rw [hankelFutureShift_column]
            exact Submodule.subset_span ⟨(p.1 + 1, p.2), rfl⟩
        | zero => simp
        | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
        | smul a x _ hx => simpa using Submodule.smul_mem _ a hx
      exact hshift v v.property)

/-- The zero-delay source, extended linearly over the input coordinates. -/
noncomputable def operatorHankelSource (K : ℕ → Matrix out inp ℂ) :
    (inp → ℂ) →ₗ[ℂ] OperatorHankelSpace K where
  toFun x := ∑ i, x i •
    (⟨operatorHankelColumn K (0, i),
      Submodule.subset_span ⟨(0, i), rfl⟩⟩ : OperatorHankelSpace K)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum]

/-- The zero-delay output evaluation. -/
def operatorHankelOutput (K : ℕ → Matrix out inp ℂ) :
    OperatorHankelSpace K →ₗ[ℂ] (out → ℂ) where
  toFun v o := (v : (ℕ × out) → ℂ) (0, o)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem operatorHankelTransition_column
    (K : ℕ → Matrix out inp ℂ) (p : ℕ × inp) :
    operatorHankelTransition K
      ⟨operatorHankelColumn K p, Submodule.subset_span ⟨p, rfl⟩⟩ =
      ⟨operatorHankelColumn K (p.1 + 1, p.2),
        Submodule.subset_span ⟨(p.1 + 1, p.2), rfl⟩⟩ := by
  apply Subtype.ext
  exact hankelFutureShift_column K p

@[simp] theorem operatorHankelSource_single
    (K : ℕ → Matrix out inp ℂ) (i : inp) :
    operatorHankelSource K (Pi.single i 1) =
      ⟨operatorHankelColumn K (0, i),
        Submodule.subset_span ⟨(0, i), rfl⟩⟩ := by
  classical
  change ∑ x, Pi.single i 1 x •
      (⟨operatorHankelColumn K (0, x),
        Submodule.subset_span ⟨(0, x), rfl⟩⟩ : OperatorHankelSpace K) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_apply, hji]
  · simp

/-- Iterating the canonical transition increments the delay label. -/
theorem operatorHankelTransition_pow_column
    (K : ℕ → Matrix out inp ℂ) (n : ℕ) (i : inp) :
    ((operatorHankelTransition K) ^ n)
      ⟨operatorHankelColumn K (0, i),
        Submodule.subset_span ⟨(0, i), rfl⟩⟩ =
      ⟨operatorHankelColumn K (n, i),
        Submodule.subset_span ⟨(n, i), rfl⟩⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih,
        operatorHankelTransition_column]

/-- The canonical source/transition/output triple realizes every kernel
coefficient exactly. -/
theorem operatorHankel_realizes_kernel
    (K : ℕ → Matrix out inp ℂ) (n : ℕ) (x : inp → ℂ) :
    operatorHankelOutput K
      (((operatorHankelTransition K) ^ n) (operatorHankelSource K x)) =
      (K n).mulVec x := by
  classical
  change operatorHankelOutput K
      (((operatorHankelTransition K) ^ n)
        (∑ i, x i • (⟨operatorHankelColumn K (0, i),
          Submodule.subset_span ⟨(0, i), rfl⟩⟩ : OperatorHankelSpace K))) = _
  simp_rw [map_sum, map_smul]
  funext o
  simp [operatorHankelTransition_pow_column, operatorHankelOutput,
    operatorHankelColumn, operatorHankelTable, Matrix.mulVec, dotProduct,
    mul_comm]

/-- All Hankel columns are reachable from the zero-delay source, hence the
canonical realization is reachable. -/
theorem operatorHankel_reachable (K : ℕ → Matrix out inp ℂ) :
    Submodule.span ℂ (Set.range fun q : ℕ × (inp → ℂ) =>
      ((operatorHankelTransition K) ^ q.1) (operatorHankelSource K q.2)) = ⊤ := by
  classical
  apply top_unique
  intro v _
  have hspan : ∀ (y : (ℕ × out) → ℂ) (hy : y ∈ OperatorHankelSpace K),
      (⟨y, hy⟩ : OperatorHankelSpace K) ∈
        Submodule.span ℂ (Set.range fun q : ℕ × (inp → ℂ) =>
          ((operatorHankelTransition K) ^ q.1)
            (operatorHankelSource K q.2)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨p, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨(p.1, Pi.single p.2 1), ?_⟩
        change ((operatorHankelTransition K) ^ p.1)
            (operatorHankelSource K (Pi.single p.2 1)) =
          (⟨operatorHankelColumn K p,
            Submodule.subset_span ⟨p, rfl⟩⟩ : OperatorHankelSpace K)
        rw [operatorHankelSource_single,
          operatorHankelTransition_pow_column]
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  exact hspan v v.property

/-- Iterated transition is future-index shift by the iteration count. -/
theorem operatorHankelTransition_pow_apply
    (K : ℕ → Matrix out inp ℂ) (n : ℕ) (v : OperatorHankelSpace K)
    (f : ℕ × out) :
    ((((operatorHankelTransition K) ^ n) v : OperatorHankelSpace K) :
        (ℕ × out) → ℂ) f =
      (v : (ℕ × out) → ℂ) (f.1 + n, f.2) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change (((((operatorHankelTransition K) ^ n) v :
          OperatorHankelSpace K) : (ℕ × out) → ℂ) (f.1 + 1, f.2)) = _
      rw [ih (f.1 + 1, f.2)]
      simp only [Nat.add_assoc, Nat.add_comm 1 n]

/-- Zero-delay outputs after all future shifts separate the canonical Hankel
state space, hence the realization is observable. -/
theorem operatorHankel_observable (K : ℕ → Matrix out inp ℂ)
    (v : OperatorHankelSpace K)
    (hv : ∀ n, operatorHankelOutput K
      (((operatorHankelTransition K) ^ n) v) = 0) :
    v = 0 := by
  apply Subtype.ext
  funext f
  have hcoord := congrFun (hv f.1) f.2
  change ((((operatorHankelTransition K) ^ f.1) v :
      OperatorHankelSpace K) : (ℕ × out) → ℂ) (0, f.2) = 0 at hcoord
  rw [operatorHankelTransition_pow_apply] at hcoord
  simpa using hcoord

/-- Finite Hankel rank constructs a reachable and observable realization of
exactly that dimension. -/
theorem finiteOperatorHankelRank_realization
    (K : ℕ → Matrix out inp ℂ) (r : ℕ)
    (hrank : Module.finrank ℂ (OperatorHankelSpace K) = r) :
    Module.finrank ℂ (OperatorHankelSpace K) = r ∧
      (∀ n x, operatorHankelOutput K
        (((operatorHankelTransition K) ^ n) (operatorHankelSource K x)) =
          (K n).mulVec x) ∧
      Submodule.span ℂ (Set.range fun q : ℕ × (inp → ℂ) =>
        ((operatorHankelTransition K) ^ q.1) (operatorHankelSource K q.2)) = ⊤ ∧
      (∀ v, (∀ n, operatorHankelOutput K
        (((operatorHankelTransition K) ^ n) v) = 0) → v = 0) := by
  exact ⟨hrank, operatorHankel_realizes_kernel K,
    operatorHankel_reachable K, operatorHankel_observable K⟩

/-! ## Minimality and uniqueness for arbitrary realizations -/

/-- The state reached from a delayed coordinate impulse in a linear
realization. -/
noncomputable def operatorRealizationPastState
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (C : (inp → ℂ) →ₗ[ℂ] N) (D : N →ₗ[ℂ] N) (p : ℕ × inp) : N :=
  (D ^ p.1) (C (Pi.single p.2 1))

/-- A future output coordinate, viewed as a scalar linear observation of the
state. -/
def operatorRealizationFutureRead
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (B : N →ₗ[ℂ] (out → ℂ)) (D : N →ₗ[ℂ] N) (f : ℕ × out) :
    N →ₗ[ℂ] ℂ where
  toFun v := B ((D ^ f.1) v) f.2
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Exact Markov parameters identify the scalar future/past table of every
realization with the intrinsic operator Hankel table. -/
theorem operatorRealization_matches_hankel
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (K : ℕ → Matrix out inp ℂ)
    (C : (inp → ℂ) →ₗ[ℂ] N) (D : N →ₗ[ℂ] N)
    (B : N →ₗ[ℂ] (out → ℂ))
    (hreal : ∀ n x, B ((D ^ n) (C x)) = (K n).mulVec x)
    (f : ℕ × out) (p : ℕ × inp) :
    operatorRealizationFutureRead B D f
        (operatorRealizationPastState C D p) =
      operatorHankelTable K f p := by
  classical
  have h := congrFun (hreal (f.1 + p.1) (Pi.single p.2 1)) f.2
  change B ((D ^ f.1) ((D ^ p.1) (C (Pi.single p.2 1)))) f.2 = _
  rw [← Module.End.mul_apply, ← pow_add]
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single p.2] at h
  · simpa [operatorHankelTable] using h
  · intro j _ hj
    simp [hj]
  · simp

/-- Every finite-dimensional realization has dimension at least the intrinsic
operator Hankel rank. -/
theorem operatorHankelRank_le_realizationDimension
    {N : Type*} [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    (K : ℕ → Matrix out inp ℂ)
    (C : (inp → ℂ) →ₗ[ℂ] N) (D : N →ₗ[ℂ] N)
    (B : N →ₗ[ℂ] (out → ℂ))
    (hreal : ∀ n x, B ((D ^ n) (C x)) = (K n).mulVec x) :
    Module.finrank ℂ (OperatorHankelSpace K) ≤ Module.finrank ℂ N := by
  exact (hankel_minimality (operatorHankelTable K)
    (operatorRealizationPastState C D)
    (operatorRealizationFutureRead B D)
    (operatorRealization_matches_hankel K C D B hreal)).2

/-- Two reachable and observable realizations of the same operator kernel are
uniquely similar.  The similarity preserves every delayed input state,
transports every future output, and intertwines the transitions. -/
theorem operatorHankel_minimalRealizations_uniquelySimilar
    {N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂]
    (K : ℕ → Matrix out inp ℂ)
    (C₁ : (inp → ℂ) →ₗ[ℂ] N₁) (D₁ : N₁ →ₗ[ℂ] N₁)
    (B₁ : N₁ →ₗ[ℂ] (out → ℂ))
    (C₂ : (inp → ℂ) →ₗ[ℂ] N₂) (D₂ : N₂ →ₗ[ℂ] N₂)
    (B₂ : N₂ →ₗ[ℂ] (out → ℂ))
    (hreal₁ : ∀ n x, B₁ ((D₁ ^ n) (C₁ x)) = (K n).mulVec x)
    (hreal₂ : ∀ n x, B₂ ((D₂ ^ n) (C₂ x)) = (K n).mulVec x)
    (hreach₁ : Submodule.span ℂ
      (Set.range (operatorRealizationPastState C₁ D₁)) = ⊤)
    (hreach₂ : Submodule.span ℂ
      (Set.range (operatorRealizationPastState C₂ D₂)) = ⊤)
    (hobs₁ : ∀ v : N₁, (∀ f,
      operatorRealizationFutureRead B₁ D₁ f v = 0) → v = 0)
    (hobs₂ : ∀ v : N₂, (∀ f,
      operatorRealizationFutureRead B₂ D₂ f v = 0) → v = 0) :
    ∃ S : N₁ ≃ₗ[ℂ] N₂,
      (∀ p, S (operatorRealizationPastState C₁ D₁ p) =
        operatorRealizationPastState C₂ D₂ p) ∧
      (∀ f v, operatorRealizationFutureRead B₂ D₂ f (S v) =
        operatorRealizationFutureRead B₁ D₁ f v) ∧
      (S : N₁ →ₗ[ℂ] N₂).comp D₁ = D₂.comp (S : N₁ →ₗ[ℂ] N₂) ∧
      (∀ G : N₁ ≃ₗ[ℂ] N₂,
        (∀ p, G (operatorRealizationPastState C₁ D₁ p) =
          operatorRealizationPastState C₂ D₂ p) → G = S) := by
  let tbl := operatorHankelTable K
  let n₁ := operatorRealizationPastState C₁ D₁
  let n₂ := operatorRealizationPastState C₂ D₂
  let ℓ₁ := operatorRealizationFutureRead B₁ D₁
  let ℓ₂ := operatorRealizationFutureRead B₂ D₂
  have hm₁ : ∀ f p, ℓ₁ f (n₁ p) = tbl f p :=
    operatorRealization_matches_hankel K C₁ D₁ B₁ hreal₁
  have hm₂ : ∀ f p, ℓ₂ f (n₂ p) = tbl f p :=
    operatorRealization_matches_hankel K C₂ D₂ B₂ hreal₂
  let S := minimalRealizationSimilarity tbl n₁ n₂ ℓ₁ ℓ₂ hm₁ hm₂
    hreach₁ hreach₂ hobs₁ hobs₂
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact minimalRealizationSimilarity_state tbl n₁ n₂ ℓ₁ ℓ₂ hm₁ hm₂
      hreach₁ hreach₂ hobs₁ hobs₂
  · exact minimalRealizationSimilarity_future tbl n₁ n₂ ℓ₁ ℓ₂ hm₁ hm₂
      hreach₁ hreach₂ hobs₁ hobs₂
  · apply minimalRealizationSimilarity_intertwines tbl n₁ n₂ ℓ₁ ℓ₂ hm₁ hm₂
      hreach₁ hreach₂ hobs₁ hobs₂ (fun p => (p.1 + 1, p.2)) D₁ D₂
    · intro p
      change D₁ ((D₁ ^ p.1) (C₁ (Pi.single p.2 1))) =
        (D₁ ^ (p.1 + 1)) (C₁ (Pi.single p.2 1))
      rw [pow_succ', Module.End.mul_apply]
    · intro p
      change D₂ ((D₂ ^ p.1) (C₂ (Pi.single p.2 1))) =
        (D₂ ^ (p.1 + 1)) (C₂ (Pi.single p.2 1))
      rw [pow_succ', Module.End.mul_apply]
  · intro G hG
    apply LinearEquiv.ext
    intro x
    have hlin := minimalRealizationSimilarity_unique tbl n₁ n₂ ℓ₁ ℓ₂ hm₁ hm₂
      hreach₁ hreach₂ hobs₁ hobs₂ G hG
    simpa [S] using LinearMap.congr_fun hlin x

end NCG
