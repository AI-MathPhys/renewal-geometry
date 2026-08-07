/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordChain

/-!
# Exact cutoff compatibility of the canonical arithmetic family
  (`thm:ar-record-cutoff`, and the canonical-record clause of
   `prop:ar-old-response`, Gran-Tensor manuscript)

* `corner_compress`: the master compression lemma — for the
  corner inclusion `J : ℂ^X → ℂ^Y` (`X ≤ Y`), the compression
  of any value-determined matrix restricts exactly:
  `Jᴴ(of f)J = of f`;
* `record_cutoff`: the boxed instances —
  `JᴴS_YJ = S_X`, `JᴴN_YJ = N_X`, and `JᴴL_{a,Y}J = L_{a,X}`
  for every `a` — the successor, count, and Peano histories are
  cutoff compatible;
* `old_response_split`: the canonical-record clause of the
  old-response comparison — with the identity endpoint Gram the
  projector is the identity, so `C_old = R_old·J` with
  `R_old = C_old·Jᴴ` and vanishing endpoint-innovation defect.

Rendering disclosed: the absorbing-corner convention for
arbitrary `*`-words and the Moore–Penrose form of the general
old-response split are the manuscript's remaining bookkeeping
(the canonical record has identity Gram, where the split is
exact as proved).
-/

open Matrix

namespace NCG

/-- The corner inclusion `ℂ^X → ℂ^Y` for `X ≤ Y`. -/
def cornerJ (X Y : ℕ) : Matrix (Fin Y) (Fin X) ℂ :=
  Matrix.of fun (j : Fin Y) (i : Fin X) =>
    if (j : ℕ) = (i : ℕ) then 1 else 0

/-- Master compression: the corner compression of any
value-determined matrix restricts exactly. -/
theorem corner_compress {X Y : ℕ} (hXY : X ≤ Y)
    (f : ℕ → ℕ → ℂ) :
    (cornerJ X Y)ᴴ
        * Matrix.of (fun (j i : Fin Y) => f (j : ℕ) (i : ℕ))
        * cornerJ X Y
      = Matrix.of (fun (j i : Fin X) => f (j : ℕ) (i : ℕ)) := by
  ext i i'
  rw [Matrix.mul_apply]
  have hinner : ∀ j' ∈ Finset.univ,
      ((cornerJ X Y)ᴴ * Matrix.of
          (fun (j i : Fin Y) => f (j : ℕ) (i : ℕ))) i j'
        * cornerJ X Y j' i'
      = if (j' : ℕ) = (i' : ℕ)
        then ((cornerJ X Y)ᴴ * Matrix.of
          (fun (j i : Fin Y) => f (j : ℕ) (i : ℕ))) i j'
        else 0 := by
    intro j' _
    simp only [cornerJ, Matrix.of_apply]
    by_cases h : (j' : ℕ) = (i' : ℕ) <;> simp [h]
  rw [Finset.sum_congr rfl hinner]
  have hi'lt : (i' : ℕ) < Y := lt_of_lt_of_le i'.isLt hXY
  rw [Finset.sum_eq_single (⟨(i' : ℕ), hi'lt⟩ : Fin Y)
    (fun j' _ hj' => by
      rw [if_neg]
      intro h
      exact hj' (Fin.ext h))
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [if_pos rfl, Matrix.mul_apply]
  have houter : ∀ j ∈ Finset.univ,
      (cornerJ X Y)ᴴ i j * Matrix.of
          (fun (j i : Fin Y) => f (j : ℕ) (i : ℕ)) j
          (⟨(i' : ℕ), hi'lt⟩ : Fin Y)
      = if (j : ℕ) = (i : ℕ)
        then f (j : ℕ) (i' : ℕ) else 0 := by
    intro j _
    simp only [cornerJ, Matrix.conjTranspose_apply,
      Matrix.of_apply]
    by_cases h : (j : ℕ) = (i : ℕ) <;> simp [h]
  rw [Finset.sum_congr rfl houter]
  have hilt : (i : ℕ) < Y := lt_of_lt_of_le i.isLt hXY
  rw [Finset.sum_eq_single (⟨(i : ℕ), hilt⟩ : Fin Y)
    (fun j _ hj => by
      rw [if_neg]
      intro h
      exact hj (Fin.ext h))
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [if_pos rfl, Matrix.of_apply]

/-- `thm:ar-record-cutoff`: the boxed compression instances —
successor, count operator, and every Peano history are cutoff
compatible. -/
theorem record_cutoff {X Y : ℕ} (hXY : X ≤ Y) (a : ℕ) :
    ((cornerJ X Y)ᴴ * recS Y * cornerJ X Y = recS X)
    ∧ ((cornerJ X Y)ᴴ
        * (Matrix.of fun (j i : Fin Y) =>
            if (j : ℕ) = (i : ℕ)
            then ((i : ℕ) + 1 : ℂ) else 0)
        * cornerJ X Y
      = Matrix.of fun (j i : Fin X) =>
          if (j : ℕ) = (i : ℕ) then ((i : ℕ) + 1 : ℂ) else 0)
    ∧ ((cornerJ X Y)ᴴ * peanoL Y a * cornerJ X Y
      = peanoL X a) := by
  refine ⟨?_, ?_, ?_⟩
  · exact corner_compress hXY
      (fun j i => if j = i + 1 then 1 else 0)
  · exact corner_compress hXY
      (fun j i => if j = i then ((i : ℕ) + 1 : ℂ) else 0)
  · exact corner_compress hXY
      (fun j i => if j + 1 = a * (i + 1) then 1 else 0)

/-- `prop:ar-old-response`, canonical-record clause: with the
identity endpoint Gram the projector is the identity, so the
old response factors exactly through the canonical endpoint
writer with vanishing innovation defect. -/
theorem old_response_split {X : ℕ} {t h : Type*} [Fintype t]
    [DecidableEq t]
    (J : Matrix (Fin X) t ℂ) (Cold : Matrix h t ℂ)
    (hGram : Jᴴ * J = 1) :
    Cold = (Cold * Jᴴ) * J
    ∧ Cold * ((1 : Matrix t t ℂ) - Jᴴ * J) = 0 := by
  constructor
  · rw [Matrix.mul_assoc, hGram, Matrix.mul_one]
  · rw [hGram, sub_self, Matrix.mul_zero]

end NCG
