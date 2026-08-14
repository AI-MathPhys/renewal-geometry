/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The locked Store supplies the faithful local K₄ source
  (`thm:dimension-locked-K4-source`,
  Gran-Tensor manuscript)

* `dimension_locked_k4_source`: for the reversal-odd
  coefficient space `P⁻` (antisymmetric coefficients
  `d_{ij} = -d_{ji}` on the twelve ordered roots
  `ρ_{ij} = e_j - e_i` of `K₄`) and the endpoint compiler
  `B(d) = ∑_{i<j} d_{ij}ρ_{ij}`:
  (i) the boxed DS.7 frame identity `BB* = 4·I` on the
      mean-zero carrier `W₀` (`B(B*w) = 4w` for `∑w = 0`,
      with `(B*w)_{ij} = w_j - w_i`);
  (ii) adjointness `⟨B*w, d⟩ = ⟨w, B(d)⟩` — giving the
      boxed orthogonal split `P⁻ = Ran B* ⊕ Ker B`;
  (iii) the boxed DS.8 for a `θ`-isometric source
      synthesis (`⟨S(d), S(d')⟩ = θ⟨d, d'⟩`): the endpoint
      triplet `S_end = S∘B*` has Gram `4θ·I` on `W₀`, the
      loop triplet `S_loop = S|_{Ker B}` keeps Gram
      `θ⟨·,·⟩`, and the two are exactly orthogonal
      (`⟨S(B*w), S(d)⟩ = 0` for `Bd = 0`).

The identification of `θ` with the intrinsic accepted
contrast weight (`cor:locked-opportunity-contrast-
spectrum`) and the invariance of ranks/margins under
another faithful future metric are the manuscript's
loading layer.
-/

open Finset

namespace NCG

/-- The endpoint compiler of the K₄ root system. -/
def k4Compiler (d : Fin 4 → Fin 4 → ℝ) :
    Fin 4 → ℝ := fun m =>
  ∑ i, ∑ j, if i < j then
    d i j * ((if m = j then 1 else 0)
      - (if m = i then 1 else 0)) else 0

/-- The coefficient pairing on the reversal-odd space. -/
def k4Pairing (d d' : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then d i j * d' i j else 0

/-- The endpoint lift `(B*w)_{ij} = w_j - w_i`. -/
def k4Lift (w : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => w j - w i

/-- `thm:dimension-locked-K4-source` (DS.7–DS.8). -/
theorem dimension_locked_k4_source :
    -- (i) the boxed DS.7 frame identity on W₀
    (∀ w : Fin 4 → ℝ, ∑ i, w i = 0 →
      k4Compiler (k4Lift w) = fun m => 4 * w m)
    -- (ii) adjointness: Ran B* ⟂ Ker B in P⁻
    ∧ (∀ (w : Fin 4 → ℝ) (d : Fin 4 → Fin 4 → ℝ),
        (∀ i j, d j i = -(d i j)) →
        k4Pairing (k4Lift w) d
          = ∑ m, w m * k4Compiler d m)
    -- (iii) the boxed DS.8 for a θ-isometric synthesis
    ∧ (∀ {V : Type} [AddCommGroup V] [Module ℝ V]
        (ip : V → V → ℝ) (S : (Fin 4 → Fin 4 → ℝ) → V)
        (θ : ℝ),
        (∀ d d', ip (S d) (S d') = θ * k4Pairing d d') →
        -- endpoint Gram 4θ on W₀
        (∀ w w' : Fin 4 → ℝ, ∑ i, w i = 0 →
          ∑ i, w' i = 0 →
          (∀ i j, k4Lift w' j i = -(k4Lift w' i j)) →
          ip (S (k4Lift w)) (S (k4Lift w'))
            = 4 * θ * ∑ m, w m * w' m)
        -- exact endpoint/loop orthogonality
        ∧ (∀ (w : Fin 4 → ℝ) (d : Fin 4 → Fin 4 → ℝ),
            (∀ i j, d j i = -(d i j)) →
            k4Compiler d = 0 →
            ip (S (k4Lift w)) (S d) = 0)) := by
  have hframe : ∀ w : Fin 4 → ℝ, ∑ i, w i = 0 →
      k4Compiler (k4Lift w) = fun m => 4 * w m := by
    intro w hw
    funext m
    rw [Fin.sum_univ_four] at hw
    rcases (by decide : ∀ x : Fin 4, x = 0 ∨ x = 1
        ∨ x = 2 ∨ x = 3) m with rfl | rfl | rfl | rfl <;>
      simp only [k4Compiler, k4Lift,
        Fin.sum_univ_four] <;>
      norm_num [Fin.lt_def, Fin.ext_iff] <;> linarith
  have hadj : ∀ (w : Fin 4 → ℝ)
      (d : Fin 4 → Fin 4 → ℝ),
      (∀ i j, d j i = -(d i j)) →
      k4Pairing (k4Lift w) d
        = ∑ m, w m * k4Compiler d m := by
    intro w d hd
    simp only [k4Pairing, k4Lift, k4Compiler,
      Fin.sum_univ_four]
    norm_num [Fin.lt_def, Fin.ext_iff]
    ring
  refine ⟨hframe, hadj, ?_⟩
  intro V _ _ ip S θ hS
  constructor
  · intro w w' hw hw' _
    rw [hS]
    rw [hadj w (k4Lift w') (fun i j => by
      simp [k4Lift])]
    rw [hframe w' hw']
    rw [show ∑ m, w m * (4 * w' m)
        = 4 * ∑ m, w m * w' m from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring]
    ring
  · intro w d hd hker
    rw [hS, hadj w d hd, hker]
    simp

end NCG
