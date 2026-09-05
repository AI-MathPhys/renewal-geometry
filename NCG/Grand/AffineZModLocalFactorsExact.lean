/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineLocalFactors
import Mathlib.Data.ZMod.Basic

/-!
# Affine local factors over residue rings

Concrete `ZMod` instantiation of the local positivity obstruction and the
Chinese-remainder density factorization.
-/

open Finset

namespace NCG
namespace AffineZModLocalFactorsExact

/-- For a prime residue packet, positivity of the normalized nonnegative
weight is exactly existence of one unobstructed residue point. -/
theorem zmod_local_positivity (p d : ℕ) [NeZero p]
    (w : (Fin d → ZMod p) → ℝ) (hw : ∀ x, 0 ≤ w x) :
    0 < (Fintype.card (Fin d → ZMod p) : ℝ)⁻¹ * ∑ x, w x ↔
      ∃ x, 0 < w x :=
  affine_local_positivity w hw

/-- The CRT equivalence on residue vectors gives exact factorization of
unobstructed counts and normalized local densities. -/
theorem zmod_chinese_remainder_density
    (m n d : ℕ) [NeZero m] [NeZero n] (hcop : m.Coprime n)
    (Pmn : (Fin d → ZMod (m * n)) → Prop)
    (Pm : (Fin d → ZMod m) → Prop)
    (Pn : (Fin d → ZMod n) → Prop)
    [DecidablePred Pmn] [DecidablePred Pm] [DecidablePred Pn]
    (hcompat : ∀ x, Pmn x ↔
      Pm (fun i => (ZMod.chineseRemainder hcop (x i)).1) ∧
      Pn (fun i => (ZMod.chineseRemainder hcop (x i)).2)) :
    ((univ.filter Pmn).card =
      (univ.filter Pm).card * (univ.filter Pn).card) ∧
    ((Fintype.card (Fin d → ZMod (m * n)) : ℝ)⁻¹ *
        (univ.filter Pmn).card =
      ((Fintype.card (Fin d → ZMod m) : ℝ)⁻¹ * (univ.filter Pm).card) *
      ((Fintype.card (Fin d → ZMod n) : ℝ)⁻¹ * (univ.filter Pn).card)
      ∨ Fintype.card (Fin d → ZMod m) = 0
      ∨ Fintype.card (Fin d → ZMod n) = 0) := by
  let e : (Fin d → ZMod (m * n)) ≃
      (Fin d → ZMod m) × (Fin d → ZMod n) :=
    (Equiv.piCongrRight fun _ => (ZMod.chineseRemainder hcop).toEquiv).trans
      (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ZMod m) (fun _ => ZMod n))
  exact affine_local_crt_factor e Pmn Pm Pn hcompat

end AffineZModLocalFactorsExact
end NCG
