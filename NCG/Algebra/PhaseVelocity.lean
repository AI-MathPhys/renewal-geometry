/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rigidity of the pairwise phase velocity

Covers `lem:phase-velocity` from `manuscripts/renewal_emergence/renewal_emergence.tex`: under the
compatible spectral phase response axioms (`ass:pair-phase-response`,
encoded as `PhaseResponse`), there is **one sign** `s ∈ {±1}` on the
block such that the pairwise angular velocity is

`ℓ_ij(a) = (s/2)(a_i − a_j)`

for every pair and every diagonal observable.  The axioms: real
linearity (P1, `add`/`smul`), scalar invariance (P1, `scalar`), pair
locality and permutation covariance (P2, `pairLocal`/`covariant`),
primitive unit contrast speed (P3, `unitSpeed`), and the triangle
identity (P4, `triangle`).

Proof, following the manuscript: linearity and pair locality give
`ℓ_ij(a) = c_ij (a_i − a_j)` after scalar invariance kills the
symmetric part (`repr`); the swap covariance makes `c` symmetric
(`coeff_symm`); the contrast normalization gives `c_ij = ±1/2`
(`coeff_half`); evaluating the triangle identity on basis vectors
propagates one coefficient through all pairs (`coeff_adj`,
`coeff_const`).  The connected nonclassical block is the whole index
type, and frame covariance is the built-in permutation covariance.
-/

namespace NCG

variable {ι : Type*} [DecidableEq ι]

/-- **Assumption `ass:pair-phase-response`**: a compatible spectral
phase response on a Jordan-frame index block. -/
structure PhaseResponse (ι : Type*) [DecidableEq ι] where
  /-- The oriented pairwise angular velocity. -/
  vel : ι → ι → (ι → ℝ) → ℝ
  add : ∀ i j a b, vel i j (a + b) = vel i j a + vel i j b
  smul : ∀ (i j : ι) (c : ℝ) (a : ι → ℝ),
    vel i j (c • a) = c * vel i j a
  scalar : ∀ (i j : ι) (c : ℝ) (a : ι → ℝ),
    vel i j (a + fun _ => c) = vel i j a
  pairLocal : ∀ i j (a a' : ι → ℝ),
    a i = a' i → a j = a' j → vel i j a = vel i j a'
  covariant : ∀ (σ : Equiv.Perm ι) (i j : ι) (a : ι → ℝ),
    vel (σ i) (σ j) (fun k => a (σ.symm k)) = vel i j a
  unitSpeed : ∀ i j, i ≠ j →
    |vel i j (fun k => if k = i then 1 else if k = j then -1
      else 0)| = 1
  triangle : ∀ (i j k : ι) (a : ι → ℝ), i ≠ j → j ≠ k → i ≠ k →
    vel i j a + vel j k a + vel k i a = 0

namespace PhaseResponse

variable (P : PhaseResponse ι)

/-- The basis vector at an index. -/
def delta (i : ι) : ι → ℝ := fun k => if k = i then 1 else 0

/-- The pair coefficient `c_ij = ℓ_ij(δ_i)`. -/
noncomputable def coeff (i j : ι) : ℝ := P.vel i j (delta i)

theorem vel_zero (i j : ι) : P.vel i j 0 = 0 := by
  have h1 := P.smul i j 0 0
  rw [zero_smul, zero_mul] at h1
  exact h1

/-- Linearity, pair locality and scalar invariance give the
antisymmetric pair representation `ℓ_ij(a) = c_ij (a_i − a_j)`. -/
theorem repr (i j : ι) (hij : i ≠ j) (a : ι → ℝ) :
    P.vel i j a = P.coeff i j * (a i - a j) := by
  have e1 : delta i i = (1 : ℝ) := if_pos rfl
  have e2 : delta j i = (0 : ℝ) := if_neg hij
  have e3 : delta i j = (0 : ℝ) := if_neg (Ne.symm hij)
  have e4 : delta j j = (1 : ℝ) := if_pos rfl
  -- ℓ_ij(δ_i) + ℓ_ij(δ_j) = ℓ_ij(1) = ℓ_ij(0) = 0
  have hone : P.vel i j (fun _ => (1 : ℝ)) = 0 := by
    have h1 := P.scalar i j 1 0
    have h2 : ((0 : ι → ℝ) + fun _ => (1 : ℝ))
        = fun _ => (1 : ℝ) := by
      funext k
      simp
    rw [h2] at h1
    rw [h1, P.vel_zero]
  have hsum : P.vel i j (delta i) + P.vel i j (delta j) = 0 := by
    have h3 : P.vel i j (delta i + delta j)
        = P.vel i j (fun _ => (1 : ℝ)) := by
      refine P.pairLocal i j _ _ ?_ ?_
      · change delta i i + delta j i = 1
        rw [e1, e2]
        norm_num
      · change delta i j + delta j j = 1
        rw [e3, e4]
        norm_num
    rw [← P.add, h3, hone]
  -- reduce a to its pair part
  have hpair : P.vel i j a
      = P.vel i j (a i • delta i + a j • delta j) := by
    refine P.pairLocal i j _ _ ?_ ?_
    · change a i = a i * delta i i + a j * delta j i
      rw [e1, e2]
      ring
    · change a j = a i * delta i j + a j * delta j j
      rw [e3, e4]
      ring
  rw [hpair, P.add, P.smul, P.smul]
  have h5 : P.coeff i j = P.vel i j (delta i) := rfl
  have h4 : P.vel i j (delta j) = -P.coeff i j := by
    rw [h5]
    linarith
  rw [h4, h5]
  ring

/-- Swap covariance makes the pair coefficient symmetric. -/
theorem coeff_symm (i j : ι) : P.coeff j i = P.coeff i j := by
  have h1 := P.covariant (Equiv.swap i j) i j (delta i)
  have h2 : (fun k => delta i ((Equiv.swap i j).symm k))
      = delta j := by
    funext k
    rw [Equiv.symm_swap]
    change (if Equiv.swap i j k = i then (1 : ℝ) else 0)
      = (if k = j then (1 : ℝ) else 0)
    by_cases hk : k = j
    · rw [if_pos hk, hk, Equiv.swap_apply_right, if_pos rfl]
    · rw [if_neg hk]
      by_cases hki : k = i
      · rw [hki, Equiv.swap_apply_left]
        exact if_neg fun hji => hk (hki.trans hji.symm)
      · rw [Equiv.swap_apply_of_ne_of_ne hki hk]
        exact if_neg hki
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right, h2] at h1
  exact h1

/-- The contrast normalization: every pair coefficient is `±1/2`. -/
theorem coeff_half (i j : ι) (hij : i ≠ j) :
    P.coeff i j = 1 / 2 ∨ P.coeff i j = -(1 / 2) := by
  have e1 : delta i i = (1 : ℝ) := if_pos rfl
  have e2 : delta j i = (0 : ℝ) := if_neg hij
  have e3 : delta i j = (0 : ℝ) := if_neg (Ne.symm hij)
  have e4 : delta j j = (1 : ℝ) := if_pos rfl
  have h1 := P.unitSpeed i j hij
  have h2 : (fun k => if k = i then (1 : ℝ) else if k = j then -1
      else 0) = fun k => delta i k - delta j k := by
    funext k
    change (if k = i then (1 : ℝ) else if k = j then -1 else 0)
      = (if k = i then (1 : ℝ) else 0)
        - (if k = j then (1 : ℝ) else 0)
    by_cases hki : k = i
    · rw [if_pos hki, if_pos hki,
        if_neg fun hkj => hij (hki.symm.trans hkj)]
      norm_num
    · rw [if_neg hki, if_neg hki]
      by_cases hkj : k = j
      · rw [if_pos hkj, if_pos hkj]
        norm_num
      · rw [if_neg hkj, if_neg hkj]
        norm_num
  have h3 : P.vel i j (fun k => delta i k - delta j k)
      = P.coeff i j * 2 := by
    rw [P.repr i j hij]
    show P.coeff i j * ((delta i i - delta j i)
        - (delta i j - delta j j)) = P.coeff i j * 2
    rw [e1, e2, e3, e4]
    ring
  rw [h2, h3] at h1
  rcases abs_cases (P.coeff i j * 2) with ⟨h5, -⟩ | ⟨h5, -⟩
  · left
    rw [h5] at h1
    linarith
  · right
    rw [h5] at h1
    linarith

/-- The triangle identity on a basis vector propagates the pair
coefficient across adjacent pairs. -/
theorem coeff_adj (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) : P.coeff i j = P.coeff j k := by
  have e1 : delta j i = (0 : ℝ) := if_neg hij
  have e2 : delta j j = (1 : ℝ) := if_pos rfl
  have e3 : delta j k = (0 : ℝ) := if_neg (Ne.symm hjk)
  have h1 := P.triangle i j k (delta j) hij hjk hik
  rw [P.repr i j hij, P.repr j k hjk, P.repr k i (Ne.symm hik),
    e1, e2, e3] at h1
  linarith

/-- One step: coefficients of pairs sharing the middle index
agree. -/
theorem coeff_step (i j l : ι) (hij : i ≠ j) (hjl : j ≠ l) :
    P.coeff i j = P.coeff j l := by
  by_cases hil : i = l
  · rw [← hil]
    exact (P.coeff_symm i j).symm
  · exact P.coeff_adj i j l hij hjl hil

/-- All pair coefficients on the block agree. -/
theorem coeff_const (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l) :
    P.coeff i j = P.coeff k l := by
  by_cases hjk : j = k
  · rw [hjk] at hij ⊢
    exact P.coeff_step i k l hij hkl
  · calc P.coeff i j = P.coeff j k := P.coeff_step i j k hij hjk
      _ = P.coeff k l := P.coeff_step j k l hjk hkl

/-- **Lemma `lem:phase-velocity`**: there is one sign `s ∈ {±1}` on
the block such that `ℓ_ij(a) = (s/2)(a_i − a_j)` for every pair and
every diagonal observable. -/
theorem phase_velocity_rigidity :
    ∃ s : ℝ, (s = 1 ∨ s = -1)
      ∧ ∀ (i j : ι) (a : ι → ℝ), i ≠ j →
          P.vel i j a = s / 2 * (a i - a j) := by
  by_cases hex : ∃ p : ι × ι, p.1 ≠ p.2
  · obtain ⟨⟨i₀, j₀⟩, h₀⟩ := hex
    refine ⟨2 * P.coeff i₀ j₀, ?_, ?_⟩
    · rcases P.coeff_half i₀ j₀ h₀ with h | h
      · left
        rw [h]
        norm_num
      · right
        rw [h]
        norm_num
    · intro i j a hij
      rw [P.repr i j hij, P.coeff_const i j i₀ j₀ hij h₀]
      ring
  · push Not at hex
    refine ⟨1, Or.inl rfl, ?_⟩
    intro i j a hij
    exact absurd (hex (i, j)) hij

end PhaseResponse

end NCG
