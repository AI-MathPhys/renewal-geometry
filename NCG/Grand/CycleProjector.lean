/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HermitianMoorePenroseInverse

/-!
# Exact harmonic cycle projector
  (`thm:cycle-projector`, Gran-Tensor manuscript)

* `cycle_projector`: for any Hermitian Penrose inverse `G` of
  the vertex Laplacian `∂∂ᴴ`, the boxed operator
  `Π_cyc = I_E - ∂ᴴG∂` is the orthogonal projection onto the
  cycle space `H₁(Γ;ℂ) = Ker ∂`: idempotent, Hermitian, kills
  under `∂`, and fixes the kernel pointwise; and rank–nullity
  gives `dim H₁ + (|V| - 1) = |E|` under the connected-graph
  rank `rank ∂ = |V| - 1`.

Rendering disclosed: `(∂∂ᴴ)†` is rendered by an arbitrary
Hermitian matrix `G` with the Penrose identities (existence of
the Moore–Penrose inverse of the Hermitian Laplacian by the
spectral theorem is not re-derived); the key range identity
`∂∂ᴴG∂ = ∂` is obtained by `MMᴴ = 0` cancellation, with no
diagonalization.  The dimension clause is stated in
subtraction-free form; that a connected graph's boundary has
rank `|V| - 1` is the manuscript's graph-theory bookkeeping.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:cycle-projector`: `Π_cyc = I - ∂ᴴ(∂∂ᴴ)†∂` is the
orthogonal projection onto the cycle space, with the
rank–nullity cycle dimension. -/
theorem cycle_projector {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E]
    (dl : Matrix V E ℂ) (G : Matrix V V ℂ) (hG : Gᴴ = G)
    (h1 : dl * dlᴴ * G * (dl * dlᴴ) = dl * dlᴴ)
    (h2 : G * (dl * dlᴴ) * G = G) :
    ((1 - dlᴴ * G * dl) * (1 - dlᴴ * G * dl)
        = 1 - dlᴴ * G * dl)
    ∧ (1 - dlᴴ * G * dl)ᴴ = 1 - dlᴴ * G * dl
    ∧ dl * (1 - dlᴴ * G * dl) = 0
    ∧ (∀ x : E → ℂ, dl *ᵥ x = 0
        → (1 - dlᴴ * G * dl) *ᵥ x = x)
    ∧ (Matrix.rank dl = Fintype.card V - 1 →
        Module.finrank ℂ (LinearMap.ker dl.mulVecLin)
          + (Fintype.card V - 1) = Fintype.card E) := by
  have h1' : dl * (dlᴴ * (G * (dl * dlᴴ))) = dl * dlᴴ := by
    have h := h1
    simp only [Matrix.mul_assoc] at h
    exact h
  have hrange : dl * dlᴴ * G * dl = dl := by
    set M := dl * dlᴴ * G * dl - dl with hM
    have hMhval : Mᴴ = dlᴴ * Gᴴ * (dl * dlᴴ) - dlᴴ := by
      rw [hM]
      simp only [Matrix.conjTranspose_sub,
        Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      congr 1
      simp only [Matrix.mul_assoc]
    have e1 : (dl * dlᴴ * G * dl) * (dlᴴ * Gᴴ * (dl * dlᴴ))
        = dl * dlᴴ := by
      rw [hG]
      simp only [Matrix.mul_assoc]
      rw [h1', h1']
    have e2 : dl * (dlᴴ * Gᴴ * (dl * dlᴴ)) = dl * dlᴴ := by
      rw [hG]
      simp only [Matrix.mul_assoc]
      rw [h1']
    have e3 : (dl * dlᴴ * G * dl) * dlᴴ = dl * dlᴴ := by
      simp only [Matrix.mul_assoc]
      rw [h1']
    have hMM : M * Mᴴ = 0 := by
      rw [hMhval, hM, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, e1, e2, e3]
      abel
    have hMh0 : Mᴴ = 0 := by
      apply Matrix.conjTranspose_mul_self_eq_zero.mp
      rw [Matrix.conjTranspose_conjTranspose]
      exact hMM
    have hM0 : M = 0 := by
      have h := congrArg Matrix.conjTranspose hMh0
      simpa using h
    have hsub : dl * dlᴴ * G * dl - dl = 0 := by
      rw [← hM]
      exact hM0
    exact sub_eq_zero.mp hsub
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hcore : dlᴴ * G * dl * (dlᴴ * G * dl)
        = dlᴴ * G * dl := by
      calc dlᴴ * G * dl * (dlᴴ * G * dl)
          = dlᴴ * (G * (dl * dlᴴ) * G) * dl := by
            simp only [Matrix.mul_assoc]
        _ = dlᴴ * G * dl := by rw [h2]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [hcore]
    abel
  · simp only [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hG]
    congr 1
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_sub, Matrix.mul_one,
      show dl * (dlᴴ * G * dl) = dl * dlᴴ * G * dl by
        simp only [Matrix.mul_assoc],
      hrange, sub_self]
  · intro x hx
    rw [Matrix.sub_mulVec, Matrix.one_mulVec,
      show (dlᴴ * G * dl) *ᵥ x = dlᴴ *ᵥ (G *ᵥ (dl *ᵥ x)) by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc],
      hx]
    simp
  · intro hrank
    have h := LinearMap.finrank_range_add_finrank_ker
      dl.mulVecLin
    rw [Module.finrank_pi] at h
    have hr : Matrix.rank dl
        = Module.finrank ℂ (LinearMap.range dl.mulVecLin) :=
      rfl
    omega

/-! ## Exact connected-incidence specialization -/

/-- Standard algebraic connectedness criterion for an oriented incidence
matrix: the only vertex potentials with zero edge gradient are constants. -/
def IsConnectedIncidence {V E : Type*} [Fintype V] [Fintype E]
    (dl : Matrix V E ℂ) : Prop :=
  dlᴴ *ᵥ (fun _ : V => (1 : ℂ)) = 0 ∧
    ∀ x : V → ℂ, dlᴴ *ᵥ x = 0 →
      ∃ c : ℂ, x = c • (fun _ : V => (1 : ℂ))

/-- Connectedness identifies the kernel of the transpose incidence with the
one-dimensional constant-potential line. -/
theorem connectedIncidence_ker_conjTranspose_eq_span_one
    {V E : Type*} [Fintype V] [Fintype E]
    (dl : Matrix V E ℂ) (hconnected : IsConnectedIncidence dl) :
    LinearMap.ker dlᴴ.mulVecLin =
      ℂ ∙ (fun _ : V => (1 : ℂ)) := by
  ext x
  constructor
  · intro hx
    have hxzero : dlᴴ *ᵥ x = 0 := LinearMap.mem_ker.mp hx
    obtain ⟨c, rfl⟩ := hconnected.2 x hxzero
    exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply LinearMap.mem_ker.mpr
    rw [map_smul]
    change c • (dlᴴ *ᵥ (fun _ : V => (1 : ℂ))) = 0
    rw [hconnected.1, smul_zero]

/-- A connected oriented incidence matrix has rank `|V|-1`; this is derived
from the constant-potential kernel, not assumed. -/
theorem connectedIncidence_rank
    {V E : Type*} [Fintype V] [Fintype E] [Nonempty V]
    (dl : Matrix V E ℂ) (hconnected : IsConnectedIncidence dl) :
    Matrix.rank dl = Fintype.card V - 1 := by
  classical
  have hone : (fun _ : V => (1 : ℂ)) ≠ 0 := by
    intro hzero
    let root : V := Classical.choice inferInstance
    have := congrFun hzero root
    simp at this
  have hker := connectedIncidence_ker_conjTranspose_eq_span_one dl hconnected
  have hnullity : Module.finrank ℂ (LinearMap.ker dlᴴ.mulVecLin) = 1 := by
    rw [hker, finrank_span_singleton hone]
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker dlᴴ.mulVecLin
  rw [hnullity, Module.finrank_pi] at hrankNullity
  have hrankTranspose : Matrix.rank dlᴴ =
      Module.finrank ℂ (LinearMap.range dlᴴ.mulVecLin) := rfl
  have hrankPlus : Matrix.rank dl + 1 = Fintype.card V := by
    rw [← Matrix.rank_conjTranspose dl, hrankTranspose]
    exact hrankNullity
  omega

/-- Exact manuscript theorem with no supplied pseudoinverse and no supplied
rank.  The spectral theorem constructs the Hermitian Moore--Penrose inverse;
connectedness derives `rank ∂ = |V|-1`; the resulting operator is precisely
the orthogonal projection onto `ker ∂`, with the cycle-dimension formula. -/
theorem exact_harmonic_cycle_projector
    {V E : Type*} [Fintype V] [Fintype E] [Nonempty V]
    [DecidableEq E]
    (dl : Matrix V E ℂ) (hconnected : IsConnectedIncidence dl) :
    ∃ G : Matrix V V ℂ,
      Gᴴ = G ∧
      (1 - dlᴴ * G * dl) * (1 - dlᴴ * G * dl) =
        1 - dlᴴ * G * dl ∧
      (1 - dlᴴ * G * dl)ᴴ = 1 - dlᴴ * G * dl ∧
      dl * (1 - dlᴴ * G * dl) = 0 ∧
      (∀ x : E → ℂ, dl *ᵥ x = 0 →
        (1 - dlᴴ * G * dl) *ᵥ x = x) ∧
      Module.finrank ℂ (LinearMap.ker dl.mulVecLin) +
          (Fintype.card V - 1) = Fintype.card E ∧
      Module.finrank ℂ (LinearMap.ker dl.mulVecLin) =
        Fintype.card E + 1 - Fintype.card V := by
  classical
  let L := dl * dlᴴ
  have hL : L.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self dl
  let G := HermitianMoorePenroseInverse.hermitianMoorePenroseInverse L hL
  have hG : Gᴴ = G :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_isHermitian L hL
  have h1 : L * G * L = L :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_penrose_left L hL
  have h2 : G * L * G = G :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_penrose_right L hL
  obtain ⟨hidempotent, hhermitian, hkill, hfix, hdimension_if⟩ :=
    cycle_projector dl G hG h1 h2
  have hrank : Matrix.rank dl = Fintype.card V - 1 :=
    connectedIncidence_rank dl hconnected
  have hdimension := hdimension_if hrank
  have hdimension_formula :
      Module.finrank ℂ (LinearMap.ker dl.mulVecLin) =
        Fintype.card E + 1 - Fintype.card V := by
    have hVpos : 0 < Fintype.card V := Fintype.card_pos
    have hsum : Module.finrank ℂ (LinearMap.ker dl.mulVecLin) +
        Fintype.card V = Fintype.card E + 1 := by
      omega
    omega
  exact ⟨G, hG, hidempotent, hhermitian, hkill, hfix,
    hdimension, hdimension_formula⟩

end NCG
