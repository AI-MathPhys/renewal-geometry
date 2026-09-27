/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.PontryaginRationalRealization

/-!
# Root subspaces of a `J`-self-adjoint operator are `J`-orthogonal

Paper `predictive_spectral_geometry`, label `thm:supp-pole-Hankel`, items (P3)
and (P4): the mechanism "Hermitian symmetry pairs a nonreal root space with its
conjugate; their indefinite form is neutral" and "the primary decomposition is
Pontryagin orthogonal".

For a finite Pontryagin realization `P` (state operator `A` with `J A = A* J`,
form `[x, y] = ⟪x, J y⟫`):

* `PontryaginRealization.form_eq_zero_of_rootSpaces`: if `(A - λ)^p x = 0`,
  `(A - μ)^q y = 0` and `μ ≠ λ̄`, then `[x, y] = 0` — root subspaces for
  spectral points which are not mutually conjugate are form-orthogonal.  In
  particular the primary decomposition of `A` is Pontryagin orthogonal up to the
  pairing of a nonreal root space with its conjugate (P4).
* `PontryaginRealization.form_self_eq_zero_of_rootSpace_nonreal`: the root
  subspace at a nonreal `λ` is neutral, `[x, x] = 0` (P3).
* `PontryaginRealization.form_eq_zero_of_rootSpaces_real`: root subspaces at
  distinct real points are orthogonal.

The remaining items of `thm:supp-pole-Hankel` (Jordan block sizes from shifted
principal-part Hankel ranks, local inertia at real poles, additivity of the
negative index over the primary decomposition) are not covered here.
-/

open scoped InnerProductSpace InnerProduct

noncomputable section

namespace RenewalGeometry

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

theorem form_sub_left (x x' y : N) : P.form (x - x') y = P.form x y - P.form x' y := by
  simp [form, inner_sub_left]

theorem form_sub_right (x y y' : N) : P.form x (y - y') = P.form x y - P.form x y' := by
  simp [form, inner_sub_right]

/-- `(A - λ) x = A x - λ x`. -/
theorem sub_algebraMap_apply (lam : ℂ) (x : N) :
    (P.A - algebraMap ℂ (N →L[ℂ] N) lam) x = P.A x - lam • x := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp

/-- The commutation relation `[(A - λ) x, y] - [x, (A - μ) y] = (μ - λ̄) [x, y]`. -/
theorem form_sub_algebraMap_comm (lam mu : ℂ) (x y : N) :
    P.form ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) x) y -
        P.form x ((P.A - algebraMap ℂ (N →L[ℂ] N) mu) y) =
      (mu - starRingEnd ℂ lam) * P.form x y := by
  rw [sub_algebraMap_apply, sub_algebraMap_apply, form_sub_left, form_sub_right, form_smul_left,
    form_smul_right, form_A_left]
  ring

/-- **Root subspaces are form-orthogonal** (`thm:supp-pole-Hankel`, (P4)
mechanism): if `(A - λ)^p x = 0`, `(A - μ)^q y = 0` and `μ ≠ λ̄`, then
`[x, y] = 0`. -/
theorem form_eq_zero_of_rootSpaces {lam mu : ℂ} (hne : mu ≠ starRingEnd ℂ lam) :
    ∀ (p q : ℕ) (x y : N), ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ p) x = 0 →
      ((P.A - algebraMap ℂ (N →L[ℂ] N) mu) ^ q) y = 0 → P.form x y = 0 := by
  intro p
  induction p with
  | zero =>
      intro q x y hx _
      rw [pow_zero, one_apply_eq_self] at hx
      rw [hx, form_zero_left]
  | succ p ihp =>
      intro q
      induction q with
      | zero =>
          intro x y _ hy
          rw [pow_zero, one_apply_eq_self] at hy
          rw [hy, form_zero_right]
      | succ q ihq =>
          intro x y hx hy
          have hx' : ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ p)
              ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) x) = 0 := by
            rw [← mul_apply_eq_comp, ← pow_succ]; exact hx
          have hy' : ((P.A - algebraMap ℂ (N →L[ℂ] N) mu) ^ q)
              ((P.A - algebraMap ℂ (N →L[ℂ] N) mu) y) = 0 := by
            rw [← mul_apply_eq_comp, ← pow_succ]; exact hy
          have h1 : P.form ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) x) y = 0 :=
            ihp (q + 1) _ y hx' hy
          have h2 : P.form x ((P.A - algebraMap ℂ (N →L[ℂ] N) mu) y) = 0 :=
            ihq x _ hx hy'
          have key := P.form_sub_algebraMap_comm lam mu x y
          rw [h1, h2, sub_zero] at key
          rcases mul_eq_zero.mp key.symm with h | h
          · exact absurd (sub_eq_zero.mp h) hne
          · exact h

/-- **Nonreal root subspaces are neutral** (`thm:supp-pole-Hankel`, (P3)):
for `Im λ ≠ 0` and `(A - λ)^p x = 0`, `[x, x] = 0`. -/
theorem form_self_eq_zero_of_rootSpace_nonreal {lam : ℂ} (hlam : lam.im ≠ 0) (p : ℕ) (x : N)
    (hx : ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ p) x = 0) : P.form x x = 0 := by
  have hne : lam ≠ starRingEnd ℂ lam := by
    intro h
    exact hlam (Complex.conj_eq_iff_im.mp h.symm)
  exact P.form_eq_zero_of_rootSpaces hne p p x x hx hx

/-- Root subspaces at distinct real points are form-orthogonal. -/
theorem form_eq_zero_of_rootSpaces_real {lam mu : ℂ} (hlam : lam.im = 0) (hne : mu ≠ lam)
    (p q : ℕ) (x y : N) (hx : ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ p) x = 0)
    (hy : ((P.A - algebraMap ℂ (N →L[ℂ] N) mu) ^ q) y = 0) : P.form x y = 0 := by
  have hne' : mu ≠ starRingEnd ℂ lam := by
    rw [Complex.conj_eq_iff_im.mpr hlam]
    exact hne
  exact P.form_eq_zero_of_rootSpaces hne' p q x y hx hy

/-- The pairing of a nonreal root space with its conjugate: `[x, y]` with
`(A - λ)^p x = 0` and `(A - μ)^q y = 0` can only be nonzero when `μ = λ̄`. -/
theorem form_ne_zero_imp_conj {lam mu : ℂ} (p q : ℕ) (x y : N)
    (hx : ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ p) x = 0)
    (hy : ((P.A - algebraMap ℂ (N →L[ℂ] N) mu) ^ q) y = 0) (h : P.form x y ≠ 0) :
    mu = starRingEnd ℂ lam := by
  by_contra hne
  exact h (P.form_eq_zero_of_rootSpaces hne p q x y hx hy)

end PontryaginRealization

end RenewalGeometry

end
