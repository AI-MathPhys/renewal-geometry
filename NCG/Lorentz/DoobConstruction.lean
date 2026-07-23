/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PerronExistence
import NCG.Lorentz.PerronPressure

/-!
# The Doob-normalized pressure law

`constr:pressure-law` (`manuscripts/renewal_emergence/renewal_emergence.tex`) for positive
transfer kernels: from the Perron data of
`NCG/Lorentz/PerronExistence.lean`,

* `doobP` — the Doob transform `P_{xy} = B_{xy} h_y / (r h_x)` of
  the kernel at its Perron root;
* `doobP_stochastic`, `doobP_pos` — `P` is a strictly positive
  stochastic edge law;
* `doobPi_stationary` (inside `pressure_law`) — the normalized
  product `π = ν h / ⟨ν, h⟩` of the left and right Perron vectors is
  a strictly positive stationary probability law for `P`;
* `perron_root_eq_pRad` — the Perron root **is** the Gelfand–Fekete
  growth rate of the eigenvector-free pressure development:
  `r = pRad B`, so `P(β) = log r` identifies the pressure with the
  Perron root;
* `pressure_law` — the assembled existence package.

The stationary-mean-depth derivative identity `μ_ℓ = −P'(β)` is not
formalized (it needs differentiability of the pressure in `β`), and
the construction is scoped to entrywise **positive** kernels (the
primitive-nonnegative case reduces by taking powers, which is not
formalized).  Downstream, this data discharges the `DoobData`
hypotheses of the entropy–affinity–depth chain.
-/

namespace NCG

open Matrix Filter

variable {n : ℕ} [NeZero n]

/-- The Doob transform of a kernel at a root `r` and gauge `h`. -/
noncomputable def doobP (B : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (h : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun x y => B x y * h y / (r * h x)

omit [NeZero n] in
theorem doobP_pos {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, 0 < B i j) {r : ℝ} (hr : 0 < r)
    {h : Fin n → ℝ} (hh : ∀ i, 0 < h i) (x y : Fin n) :
    0 < doobP B r h x y := by
  rw [doobP, Matrix.of_apply]
  exact div_pos (mul_pos (hB x y) (hh y)) (mul_pos hr (hh x))

omit [NeZero n] in
/-- **The Doob law is stochastic** at a right Perron pair. -/
theorem doobP_stochastic {B : Matrix (Fin n) (Fin n) ℝ} {r : ℝ}
    (hr : 0 < r) {h : Fin n → ℝ} (hh : ∀ i, 0 < h i)
    (heig : B.mulVec h = r • h) (x : Fin n) :
    ∑ y, doobP B r h x y = 1 := by
  have h1 : ∑ y, doobP B r h x y
      = (∑ y, B x y * h y) / (r * h x) := by
    rw [Finset.sum_div]
    rfl
  have h2 : ∑ y, B x y * h y = r * h x := by
    have h3 := congrFun heig x
    rw [Matrix.mulVec, dotProduct] at h3
    rw [h3, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  exact div_self (mul_pos hr (hh x)).ne'

/-- **The Perron root is the Gelfand–Fekete growth rate** for a
positive kernel — the special case of `NCG.eigenvalue_eq_pRad`, so
the pressure of the eigenvector-free development is `log r`. -/
theorem perron_root_eq_pRad {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, 0 < B i j) {r : ℝ} (hr : 0 < r)
    {h : Fin n → ℝ} (hh : ∀ i, 0 < h i)
    (heig : B.mulVec h = r • h) :
    r = pRad B :=
  eigenvalue_eq_pRad (fun i j => (hB i j).le)
    ⟨Classical.arbitrary (Fin n), 1, one_pos, by
      rw [pow_one]; exact hB _ _⟩ hr hh heig

/-- **Construction `constr:pressure-law`** for positive transfer
kernels: the full Doob package — Perron root and gauges, strictly
positive stochastic edge law, and strictly positive stationary
probability weight. -/
theorem pressure_law {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, 0 < B i j) :
    ∃ (r : ℝ) (h ν : Fin n → ℝ) (π : Fin n → ℝ),
      0 < r ∧ (∀ i, 0 < h i) ∧ (∀ i, 0 < ν i)
        ∧ B.mulVec h = r • h ∧ B.vecMul ν = r • ν
        ∧ (∀ x y, 0 < doobP B r h x y)
        ∧ (∀ x, ∑ y, doobP B r h x y = 1)
        ∧ (∀ i, 0 < π i) ∧ (∑ i, π i = 1)
        ∧ (∀ y, ∑ x, π x * doobP B r h x y = π y)
        ∧ r = pRad B := by
  classical
  obtain ⟨r, h, hr, hh, heig⟩ := exists_pos_eigenvector_of_pos hB
  obtain ⟨s, ν, hs, hν, heig'⟩ := exists_pos_left_eigenvector_of_pos hB
  have hrs : r = s := left_right_eigenvalue_eq hh hν heig heig'
  subst hrs
  set Z := ∑ i, ν i * h i with hZ
  have hZpos : 0 < Z := by
    rw [hZ]
    exact Finset.sum_pos (fun i _ => mul_pos (hν i) (hh i))
      Finset.univ_nonempty
  refine ⟨r, h, ν, fun i => ν i * h i / Z, hr, hh, hν, heig,
    heig', fun x y => doobP_pos hB hr hh x y,
    fun x => doobP_stochastic hr hh heig x,
    fun i => div_pos (mul_pos (hν i) (hh i)) hZpos, ?_, ?_,
    perron_root_eq_pRad hB hr hh heig⟩
  · rw [← Finset.sum_div, ← hZ]
    exact div_self hZpos.ne'
  · intro y
    have h1 : ∀ x, ν x * h x / Z * doobP B r h x y
        = ν x * B x y * h y / (r * Z) := by
      intro x
      rw [doobP, Matrix.of_apply]
      field_simp [(hh x).ne']
    rw [Finset.sum_congr rfl fun x _ => h1 x]
    have h2 : ∑ x, ν x * B x y * h y / (r * Z)
        = (∑ x, ν x * B x y) * h y / (r * Z) := by
      rw [Finset.sum_mul, Finset.sum_div]
    rw [h2]
    have h3 : ∑ x, ν x * B x y = r * ν y := by
      have h4 := congrFun heig' y
      rw [Matrix.vecMul, dotProduct] at h4
      rw [h4, Pi.smul_apply, smul_eq_mul]
    rw [h3]
    field_simp [(hh y).ne']

end NCG
