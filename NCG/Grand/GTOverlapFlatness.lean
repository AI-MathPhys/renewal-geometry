/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Zero-innovation overlap is pure gauge
  (`thm:GT-source-overlap-flatness`,
  Gran-Tensor manuscript)

* `gt_source_overlap_flatness`: for whitened equal-rank
  source profiles `Vᵢ` (isometries) whose ranges all
  coincide (the zero-innovation-in-both-directions
  hypothesis on every edge), the normalized overlaps
  `W_{j←i} = Vⱼ*Vᵢ` are
  (i) unitary on every edge,
  (ii) of the boxed pure-gauge form `W_{j←i} = Qⱼ*Qᵢ` with
      vertex unitaries `Qᵢ = V_{i₀}*Vᵢ` (any base
      vertex), and
  (iii) an exactly flat cocycle,
      `W_{k←j}W_{j←i} = W_{k←i}` and `W_{i←i} = 1` — so
      the boxed `W(C) = 1` holds for every cycle by
      telescoping.

Hence nontrivial physical holonomy cannot be inferred from
a globally glued zero-innovation source atlas.  The
reduction from per-edge zero source-range innovation to the
common range projection, and the whitening itself, are the
manuscript's normalization layer.
-/

open Matrix

namespace NCG

/-- `thm:GT-source-overlap-flatness` (SK.4). -/
theorem gt_source_overlap_flatness {ι n r : Type}
    [Fintype n] [Fintype r] [DecidableEq r]
    (V : ι → Matrix n r ℂ)
    (hiso : ∀ i, (V i)ᴴ * V i = 1)
    (hrange : ∀ i j, V i * (V i)ᴴ = V j * (V j)ᴴ)
    (i0 : ι) :
    -- (i) every edge overlap is unitary
    (∀ i j, ((V j)ᴴ * V i)ᴴ * ((V j)ᴴ * V i) = 1
      ∧ ((V j)ᴴ * V i) * ((V j)ᴴ * V i)ᴴ = 1)
    -- (ii) the boxed pure-gauge form W_{j←i} = Qⱼ*Qᵢ
    ∧ (∀ i j, (V j)ᴴ * V i
        = ((V i0)ᴴ * V j)ᴴ * ((V i0)ᴴ * V i))
    -- (iii) exactly flat cocycle (all cycles trivial)
    ∧ (∀ i j k, ((V k)ᴴ * V j) * ((V j)ᴴ * V i)
        = (V k)ᴴ * V i)
    ∧ (∀ i, (V i)ᴴ * V i = 1) := by
  have hkey : ∀ j i, V j * ((V j)ᴴ * V i) = V i := by
    intro j i
    rw [← Matrix.mul_assoc, hrange j i,
      Matrix.mul_assoc, hiso i, Matrix.mul_one]
  have hcocycle : ∀ i j k,
      ((V k)ᴴ * V j) * ((V j)ᴴ * V i)
        = (V k)ᴴ * V i := by
    intro i j k
    calc ((V k)ᴴ * V j) * ((V j)ᴴ * V i)
        = (V k)ᴴ * (V j * ((V j)ᴴ * V i)) := by
          simp only [Matrix.mul_assoc]
      _ = (V k)ᴴ * V i := by rw [hkey j i]
  refine ⟨?_, ?_, hcocycle, hiso⟩
  · intro i j
    constructor
    · calc ((V j)ᴴ * V i)ᴴ * ((V j)ᴴ * V i)
          = ((V i)ᴴ * V j) * ((V j)ᴴ * V i) := by
            rw [Matrix.conjTranspose_mul,
              Matrix.conjTranspose_conjTranspose]
        _ = (V i)ᴴ * V i := hcocycle i j i
        _ = 1 := hiso i
    · calc ((V j)ᴴ * V i) * ((V j)ᴴ * V i)ᴴ
          = ((V j)ᴴ * V i) * ((V i)ᴴ * V j) := by
            rw [Matrix.conjTranspose_mul,
              Matrix.conjTranspose_conjTranspose]
        _ = (V j)ᴴ * V j := hcocycle j i j
        _ = 1 := hiso j
  · intro i j
    calc (V j)ᴴ * V i
        = ((V j)ᴴ * V i0) * ((V i0)ᴴ * V i) :=
          (hcocycle i i0 j).symm
      _ = ((V i0)ᴴ * V j)ᴴ * ((V i0)ᴴ * V i) := by
          rw [Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]

end NCG
