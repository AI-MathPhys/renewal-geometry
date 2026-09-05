/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Accessibility independence family
  (`prop:vertical-independence`, SM manuscript)

For the vertical partial isometries `F_{x,R} = |x,L⟩⟨x,R| ⊗ I₄`,
`F_{x,L} = F_{x,R}†`, the dissipator

  `𝒟(ρ) = Σ_{x,χ} F_{x,χ} ρ F_{x,χ}† - ρ`

is trace preserving, unital, tracially symmetric, and invisible to
the classical diagonal six-label process, while its accessibility
effects are the boxed `A_{L←R} = λ P_L`, `A_{R←L} = λ P_R` for the
family `𝓛_λ = 𝓛_bare + λ𝒟`: the label law and scalar gain cocycle
are identical for all `λ`, and charged accessibility is absent at
`λ = 0` and present for every `λ > 0`.

Here the family is encoded by its `R→L` movers `G x` (so
`F_{x,R} = G x`, `F_{x,L} = (G x)ᴴ`), and the partial-isometry
structure of the displayed operators enters through the hypotheses
`P_L G P_R = G`, `Σ G G† = P_L`, `Σ G† G = P_R`, label commutation,
and the projection identities — all exact identities of the
manuscript's `|x,L⟩⟨x,R| ⊗ I₄` (disclosed model choice).  The bare
generator enters only through its hypothesized vanishing charged
compressions (the preceding displayed corollary).
-/

open Matrix

namespace NCG

variable {n m ι : Type*} [Fintype n] [Fintype m]

/-- The vertical dissipator built from the `R→L` movers `G` and
their adjoints. -/
noncomputable def vertDissipator (G : m → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  (∑ x, (G x * ρ * (G x)ᴴ + (G x)ᴴ * ρ * G x)) - ρ

variable (G : m → Matrix n n ℂ) (PL PR : Matrix n n ℂ)

/-- The dissipator is trace preserving. -/
lemma vertDissipator_trace [DecidableEq n]
    (hGGh : ∑ x, G x * (G x)ᴴ = PL)
    (hGhG : ∑ x, (G x)ᴴ * G x = PR) (hsum1 : PL + PR = 1)
    (ρ : Matrix n n ℂ) :
    (vertDissipator G ρ).trace = 0 := by
  rw [vertDissipator, Matrix.trace_sub, Matrix.trace_sum]
  have h : ∀ x : m, (G x * ρ * (G x)ᴴ + (G x)ᴴ * ρ * G x).trace
      = ((G x)ᴴ * G x * ρ).trace + (G x * (G x)ᴴ * ρ).trace := by
    intro x
    rw [Matrix.trace_add, Matrix.trace_mul_cycle (G x) ρ (G x)ᴴ,
      Matrix.trace_mul_cycle (G x)ᴴ ρ (G x)]
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_add_distrib,
    ← Matrix.trace_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
    ← Finset.sum_mul, hGhG, hGGh, ← Matrix.trace_add, ← Matrix.add_mul,
    add_comm PR PL, hsum1, Matrix.one_mul, sub_self]

/-- The dissipator is unital. -/
lemma vertDissipator_one [DecidableEq n]
    (hGGh : ∑ x, G x * (G x)ᴴ = PL)
    (hGhG : ∑ x, (G x)ᴴ * G x = PR) (hsum1 : PL + PR = 1) :
    vertDissipator G 1 = 0 := by
  rw [vertDissipator]
  simp only [Matrix.mul_one]
  rw [Finset.sum_add_distrib, hGGh, hGhG, hsum1, sub_self]

/-- The dissipator is tracially symmetric. -/
lemma vertDissipator_symm (ρ σ : Matrix n n ℂ) :
    ((vertDissipator G ρ) * σ).trace
      = (ρ * vertDissipator G σ).trace := by
  rw [vertDissipator, vertDissipator, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.trace_sub, Finset.sum_mul,
    Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : (G x * ρ * (G x)ᴴ * σ).trace
      = (ρ * ((G x)ᴴ * σ * G x)).trace := by
    rw [show G x * ρ * (G x)ᴴ * σ = (G x * ρ) * ((G x)ᴴ * σ) by
        simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show (G x)ᴴ * σ * (G x * ρ) = ((G x)ᴴ * σ * G x) * ρ by
        simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
  have h2 : ((G x)ᴴ * ρ * G x * σ).trace
      = (ρ * (G x * σ * (G x)ᴴ)).trace := by
    rw [show (G x)ᴴ * ρ * G x * σ = ((G x)ᴴ * ρ) * (G x * σ) by
        simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show G x * σ * ((G x)ᴴ * ρ) = (G x * σ * (G x)ᴴ) * ρ by
        simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_add, h1, h2, add_comm]

variable (Q : ι → Matrix n n ℂ)

omit [Fintype m] in
/-- The label projections also commute with the adjoint movers. -/
lemma label_comm_adjoint (hQcomm : ∀ y x, Q y * G x = G x * Q y)
    (hQh : ∀ y, (Q y)ᴴ = Q y) (y : ι) (x : m) :
    Q y * (G x)ᴴ = (G x)ᴴ * Q y := by
  have h := congrArg Matrix.conjTranspose (hQcomm y x)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQh] at h
  exact h.symm

/-- The dissipator is invisible to the classical diagonal label
process: every label effect has zero response. -/
lemma vertDissipator_label [DecidableEq n]
    (hGGh : ∑ x, G x * (G x)ᴴ = PL)
    (hGhG : ∑ x, (G x)ᴴ * G x = PR) (hsum1 : PL + PR = 1)
    (hQcomm : ∀ y x, Q y * G x = G x * Q y)
    (hQh : ∀ y, (Q y)ᴴ = Q y) (y : ι) (ρ : Matrix n n ℂ) :
    (Q y * vertDissipator G ρ).trace = 0 := by
  rw [vertDissipator, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_sum, Matrix.trace_sum]
  have h : ∀ x : m, (Q y * (G x * ρ * (G x)ᴴ + (G x)ᴴ * ρ * G x)).trace
      = ((G x)ᴴ * G x * (Q y * ρ)).trace
        + (G x * (G x)ᴴ * (Q y * ρ)).trace := by
    intro x
    rw [Matrix.mul_add, Matrix.trace_add]
    congr 1
    · rw [show Q y * (G x * ρ * (G x)ᴴ) = (Q y * G x) * ρ * (G x)ᴴ by
          simp [Matrix.mul_assoc],
        hQcomm y x,
        Matrix.trace_mul_cycle (G x * Q y) ρ (G x)ᴴ,
        show (G x)ᴴ * (G x * Q y) * ρ = (G x)ᴴ * G x * (Q y * ρ) by
          simp [Matrix.mul_assoc]]
    · rw [show Q y * ((G x)ᴴ * ρ * G x) = (Q y * (G x)ᴴ) * ρ * G x by
          simp [Matrix.mul_assoc],
        label_comm_adjoint G Q hQcomm hQh y x,
        Matrix.trace_mul_cycle ((G x)ᴴ * Q y) ρ (G x),
        show G x * ((G x)ᴴ * Q y) * ρ = G x * (G x)ᴴ * (Q y * ρ) by
          simp [Matrix.mul_assoc]]
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_add_distrib,
    ← Matrix.trace_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
    ← Finset.sum_mul, hGhG, hGGh, ← Matrix.trace_add, ← Matrix.add_mul,
    add_comm PR PL, hsum1, Matrix.one_mul, sub_self]

omit [Fintype m] in
/-- The movers absorb the right support. -/
lemma mover_mul_PR (hPR2 : PR * PR = PR)
    (hGsupp : ∀ x, PL * G x * PR = G x) (x : m) : G x * PR = G x := by
  calc G x * PR = PL * G x * PR * PR := by rw [hGsupp x]
    _ = PL * G x * (PR * PR) := by rw [Matrix.mul_assoc]
    _ = PL * G x * PR := by rw [hPR2]
    _ = G x := hGsupp x

omit [Fintype m] in
/-- The movers are annihilated by the right support on the left. -/
lemma PR_mul_mover (hRL : PR * PL = 0)
    (hGsupp : ∀ x, PL * G x * PR = G x) (x : m) : PR * G x = 0 := by
  calc PR * G x = PR * (PL * G x * PR) := by rw [hGsupp x]
    _ = (PR * PL) * (G x * PR) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc]
    _ = 0 := by rw [hRL, Matrix.zero_mul]

omit [Fintype m] in
/-- The movers absorb the left support. -/
lemma PL_mul_mover (hPL2 : PL * PL = PL)
    (hGsupp : ∀ x, PL * G x * PR = G x) (x : m) : PL * G x = G x := by
  calc PL * G x = PL * (PL * G x * PR) := by rw [hGsupp x]
    _ = (PL * PL) * (G x * PR) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc]
    _ = G x := by rw [hPL2, ← Matrix.mul_assoc]; exact hGsupp x

omit [Fintype m] in
/-- The movers are annihilated by the left support on the right. -/
lemma mover_mul_PL (hRL : PR * PL = 0)
    (hGsupp : ∀ x, PL * G x * PR = G x) (x : m) : G x * PL = 0 := by
  calc G x * PL = (PL * G x * PR) * PL := by rw [hGsupp x]
    _ = (PL * G x) * (PR * PL) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hRL, Matrix.mul_zero]

/-- Compression value: `𝒟(P_R) = P_L - P_R`. -/
lemma vertDissipator_PR (hGGh : ∑ x, G x * (G x)ᴴ = PL)
    (hPRh : PRᴴ = PR) (hPR2 : PR * PR = PR) (hRL : PR * PL = 0)
    (hGsupp : ∀ x, PL * G x * PR = G x) :
    vertDissipator G PR = PL - PR := by
  rw [vertDissipator]
  have h : ∀ x : m, G x * PR * (G x)ᴴ + (G x)ᴴ * PR * G x
      = G x * (G x)ᴴ := by
    intro x
    have hGh : (G x)ᴴ * PR = 0 := by
      have h0 := congrArg Matrix.conjTranspose
        (PR_mul_mover G PL PR hRL hGsupp x)
      rw [Matrix.conjTranspose_mul, hPRh,
        Matrix.conjTranspose_zero] at h0
      exact h0
    rw [mover_mul_PR G PL PR hPR2 hGsupp x, hGh, Matrix.zero_mul,
      add_zero]
  rw [Finset.sum_congr rfl fun x _ => h x, hGGh]

/-- Compression value: `𝒟(P_L) = P_R - P_L`. -/
lemma vertDissipator_PL (hGhG : ∑ x, (G x)ᴴ * G x = PR)
    (hPLh : PLᴴ = PL) (hPL2 : PL * PL = PL) (hRL : PR * PL = 0)
    (hGsupp : ∀ x, PL * G x * PR = G x) :
    vertDissipator G PL = PR - PL := by
  rw [vertDissipator]
  have h : ∀ x : m, G x * PL * (G x)ᴴ + (G x)ᴴ * PL * G x
      = (G x)ᴴ * G x := by
    intro x
    have hGh : (G x)ᴴ * PL = (G x)ᴴ := by
      have h0 := congrArg Matrix.conjTranspose
        (PL_mul_mover G PL PR hPL2 hGsupp x)
      rw [Matrix.conjTranspose_mul, hPLh] at h0
      exact h0
    rw [mover_mul_PL G PL PR hRL hGsupp x, Matrix.zero_mul, zero_add,
      hGh]
  rw [Finset.sum_congr rfl fun x _ => h x, hGhG]

/-- `prop:vertical-independence`, boxed accessibility effects: for
the family `𝓛_λ = 𝓛_bare + λ𝒟` with charged-invisible bare part,
`A_{L←R} = λ P_L` and `A_{R←L} = λ P_R`; charged accessibility is
absent at `λ = 0` and present for every `λ > 0`. -/
theorem vertical_independence
    (hGGh : ∑ x, G x * (G x)ᴴ = PL)
    (hGhG : ∑ x, (G x)ᴴ * G x = PR)
    (hPLh : PLᴴ = PL) (hPRh : PRᴴ = PR)
    (hPL2 : PL * PL = PL) (hPR2 : PR * PR = PR)
    (hLR : PL * PR = 0) (hRL : PR * PL = 0)
    (hGsupp : ∀ x, PL * G x * PR = G x)
    (Lbare : Matrix n n ℂ → Matrix n n ℂ) (lam : ℝ)
    (hbareLR : PL * Lbare PR * PL = 0)
    (hbareRL : PR * Lbare PL * PR = 0) (hPLne : PL ≠ 0) :
    (PL * (Lbare PR + (lam : ℂ) • vertDissipator G PR) * PL
      = (lam : ℂ) • PL)
    ∧ (PR * (Lbare PL + (lam : ℂ) • vertDissipator G PL) * PR
      = (lam : ℂ) • PR)
    ∧ ((lam : ℂ) • PL = 0 ↔ lam = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vertDissipator_PR G PL PR hGGh hPRh hPR2 hRL hGsupp,
      Matrix.mul_add, Matrix.add_mul, hbareLR, zero_add,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, hPL2, hLR,
      sub_zero, hPL2]
  · rw [vertDissipator_PL G PL PR hGhG hPLh hPL2 hRL hGsupp,
      Matrix.mul_add, Matrix.add_mul, hbareRL, zero_add,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, hPR2, hRL,
      sub_zero, hPR2]
  · rw [smul_eq_zero]
    constructor
    · rintro (h | h)
      · exact_mod_cast h
      · exact absurd h hPLne
    · intro h
      rw [h]
      norm_num

end NCG
