/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.DetCrossing

/-!
# Endpoint path parity: homotopy invariance and multiplicativity

Definition `def:determinant-path-parity` and clauses (i)–(iii) of
Theorem `thm:determinant-path-parity` (`manuscripts/renewal_emergence/renewal_emergence.tex`) in
the additive `ℤ/2` orientation calculus of
`NCG/Lorentz/DetCrossing.lean`:

* `pathParity` — the endpoint parity
  `par(Q) = sgn det Q_b · sgn det Q_a` in additive form
  `orSign (det Q_a) + orSign (det Q_b)`;
* `pathParity_conjugate` — independence from the orientation
  (basis) choices at source and target: conjugating the whole path
  by fixed invertible frame changes leaves the parity unchanged;
* `pathParity_homotopy_invariant` — clause (i): invariance under
  homotopies through paths with invertible endpoints;
* `pathParity_concat` — clause (ii): multiplicativity under path
  concatenation;
* `pathParity_eq_crossing_count` — the boxed crossing formula of
  clause (iii) in the regular normal form: for a `C¹` path with
  finitely many transverse crossings the parity equals the crossing
  count mod two (each transverse matrix crossing has
  one-dimensional kernel).

The remaining content of clause (iii) — existence of an arbitrarily
small endpoint-fixed perturbation with finitely many regular
crossings (finite-dimensional stratified transversality) — and the
qualitative clauses (iv)–(v) are not formalized here.
-/

namespace NCG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Set

/-- **Definition `def:determinant-path-parity`** in additive `ℤ/2`
form: the endpoint parity of a determinant path. -/
noncomputable def pathParity {r : ℕ}
    (L : ℝ → Matrix (Fin r) (Fin r) ℝ) (a b : ℝ) : ZMod 2 :=
  orSign ((L a).det) + orSign ((L b).det)

/-- **Orientation independence** (`def:determinant-path-parity`):
conjugating the path by fixed invertible frame changes of source and
target leaves the endpoint parity unchanged — the two orientation
sign contributions appear at both endpoints and cancel mod two. -/
theorem pathParity_conjugate {r : ℕ}
    (L : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (C₁ C₂ : Matrix (Fin r) (Fin r) ℝ)
    (hC₁ : C₁.det ≠ 0) (hC₂ : C₂.det ≠ 0) {a b : ℝ}
    (ha : (L a).det ≠ 0) (hb : (L b).det ≠ 0) :
    pathParity (fun t => C₁ * L t * C₂) a b = pathParity L a b := by
  unfold pathParity
  have h1 : ∀ t : ℝ, (L t).det ≠ 0 →
      orSign ((C₁ * L t * C₂).det)
        = orSign C₁.det + orSign ((L t).det) + orSign C₂.det := by
    intro t ht
    rw [Matrix.det_mul, Matrix.det_mul, orSign_mul
      (mul_ne_zero hC₁ ht) hC₂, orSign_mul hC₁ ht]
  rw [h1 a ha, h1 b hb]
  have h2 : orSign C₁.det + orSign C₁.det = 0 :=
    CharTwo.add_self_eq_zero _
  have h3 : orSign C₂.det + orSign C₂.det = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination h2 + h3

/-- **Theorem `thm:determinant-path-parity` (i)**: the endpoint
parity is invariant under homotopies through paths with invertible
endpoints — neither endpoint determinant can cross zero. -/
theorem pathParity_homotopy_invariant {r : ℕ}
    {F : ℝ → ℝ → Matrix (Fin r) (Fin r) ℝ} {a b s₀ s₁ : ℝ}
    (hs : s₀ ≤ s₁)
    (hca : Continuous fun s => F s a)
    (hcb : Continuous fun s => F s b)
    (hia : ∀ s ∈ Set.Icc s₀ s₁, (F s a).det ≠ 0)
    (hib : ∀ s ∈ Set.Icc s₀ s₁, (F s b).det ≠ 0) :
    pathParity (F s₀) a b = pathParity (F s₁) a b := by
  unfold pathParity
  rw [orSign_eq_of_forall_ne hca.matrix_det hs hia,
    orSign_eq_of_forall_ne hcb.matrix_det hs hib]

/-- **Theorem `thm:determinant-path-parity` (ii)**: the endpoint
parity is multiplicative (additive mod two) under path
concatenation — the determinant sign at the common endpoint appears
twice and cancels. -/
theorem pathParity_concat {r : ℕ}
    (L : ℝ → Matrix (Fin r) (Fin r) ℝ) (a b c : ℝ) :
    pathParity L a b + pathParity L b c = pathParity L a c := by
  unfold pathParity
  have h1 : orSign ((L b).det) + orSign ((L b).det) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination h1

/-- **Theorem `thm:determinant-path-parity` (iii), regular normal
form**: for a `C¹` path whose determinant zeros are finitely many
transverse crossings — the corank-one stratum, where each crossing
kernel is one-dimensional — the endpoint parity is the crossing
count mod two: `par(Q) = (−1)^{Σ dim ker}`. -/
theorem pathParity_eq_crossing_count {r : ℕ}
    {L : ℝ → Matrix (Fin r) (Fin r) ℝ} (hL : ContDiff ℝ 1 L)
    {a b : ℝ} (hab : a ≤ b)
    (hfa : (L a).det ≠ 0) (hfb : (L b).det ≠ 0)
    (Z : Finset ℝ) (hZ : ∀ z ∈ Z, z ∈ Set.Ioo a b)
    (hoff : ∀ x ∈ Set.Icc a b, x ∉ Z → (L x).det ≠ 0)
    (hzero : ∀ z ∈ Z, (L z).det = 0)
    (htrans : ∀ z ∈ Z, deriv (fun t => (L t).det) z ≠ 0) :
    pathParity L a b = (Z.card : ZMod 2) := by
  unfold pathParity
  rw [det_crossing_parity hL hab hfa hfb Z hZ hoff hzero htrans]
  have h1 : orSign ((L a).det) + orSign ((L a).det) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination h1

/-- **The stratified-transversality interface**
(`thm:determinant-path-parity` (iii), existence half — the
finite-dimensional transversality principle of
Fitzpatrick–Pejsachowicz and Doll–Schulz-Baldes–Waterstraat, the
scoped literature input): an endpoint-fixed `C¹` perturbation of the
path whose determinant zeros are finitely many transverse
crossings. -/
structure RegularPerturbation {r : ℕ}
    (L : ℝ → Matrix (Fin r) (Fin r) ℝ) (a b : ℝ) where
  /-- The perturbed path. -/
  L' : ℝ → Matrix (Fin r) (Fin r) ℝ
  /-- Regularity. -/
  contDiff : ContDiff ℝ 1 L'
  /-- The perturbation fixes the endpoints. -/
  endpoint_a : L' a = L a
  /-- The perturbation fixes the endpoints. -/
  endpoint_b : L' b = L b
  /-- The finitely many crossings. -/
  Z : Finset ℝ
  interior : ∀ z ∈ Z, z ∈ Set.Ioo a b
  off_zeros : ∀ x ∈ Set.Icc a b, x ∉ Z → (L' x).det ≠ 0
  at_zeros : ∀ z ∈ Z, (L' z).det = 0
  transverse : ∀ z ∈ Z, deriv (fun t => (L' t).det) z ≠ 0

/-- **Theorem `thm:determinant-path-parity` (iii), assembled**: for
**every** endpoint-fixed regular perturbation, the boxed crossing
formula holds for the original endpoint parity —
`par(Q) = (−1)^{Σ_t dim ker Q̃_t}` (each transverse matrix crossing
has one-dimensional kernel).  Independence of the chosen
perturbation is immediate: the left side never mentions it. -/
theorem pathParity_eq_perturbed_crossing_count {r : ℕ}
    {L : ℝ → Matrix (Fin r) (Fin r) ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfa : (L a).det ≠ 0) (hfb : (L b).det ≠ 0)
    (P : RegularPerturbation L a b) :
    pathParity L a b = (P.Z.card : ZMod 2) := by
  have h1 : pathParity P.L' a b = pathParity L a b := by
    unfold pathParity
    rw [P.endpoint_a, P.endpoint_b]
  rw [← h1]
  refine pathParity_eq_crossing_count P.contDiff hab ?_ ?_
    P.Z P.interior P.off_zeros P.at_zeros P.transverse
  · rw [P.endpoint_a]
    exact hfa
  · rw [P.endpoint_b]
    exact hfb

end NCG
