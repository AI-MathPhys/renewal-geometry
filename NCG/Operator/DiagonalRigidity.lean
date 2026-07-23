/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Operator.Diagonal

/-!
# Atomic-diagonal rigidity and finite propagation

**Lemma `lem:atom`** (rigidity core): the atomic diagonal algebra is
maximal abelian in the algebraic model — an operator commuting with
**all** diagonal multipliers is itself diagonal:
`T e_x = (T e_x)(x)·e_x` (`NCG.diagonal_commutant`).  This is the
mechanism behind the reconstruction theorem: a unitary intertwining the
atomic diagonals must permute the basis rays up to phases.  (The
minimal-projection/phase packaging on `ℓ²` is not formalised.)

**Definition `def:finite-propagation`**: an operator has propagation
`≤ r` when its matrix coefficients vanish beyond distance `r`
(`NCG.HasPropagation`); diagonal multipliers have propagation `0`
(`NCG.diagOp_hasPropagation_zero`) and lifted shifts along
distance-`≤ 1` maps have propagation `1`
(`NCG.shiftOp_hasPropagation_one`) — the generators of the
finite-propagation renewal algebra. -/

namespace NCG

variable {ι : Type*} [DecidableEq ι]

/-- Pointwise formula for the diagonal operator:
`(diagOp d f)(j) = d(j)·f(j)`. -/
theorem diagOp_apply (d : ι → ℂ) (f : ι →₀ ℂ) (j : ι) :
    (diagOp d f) j = d j * f j := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg, mul_add]
  | single i c =>
      rw [diagOp_single]
      rcases eq_or_ne i j with rfl | hij
      · simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, hij]

/-- **Lemma `lem:atom`** (diagonal-commutant rigidity): an operator
commuting with every diagonal multiplier is diagonal — it maps each
basis ray into itself.  The atomic diagonal is maximal abelian, which
is what forces intertwining unitaries to act by a basis bijection and
phases. -/
theorem diagonal_commutant (T : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ))
    (hT : ∀ d : ι → ℂ, T ∘ₗ diagOp d = diagOp d ∘ₗ T) (x : ι) :
    T (Finsupp.single x 1)
      = Finsupp.single x ((T (Finsupp.single x 1)) x) := by
  have h := congrArg (fun L => L (Finsupp.single x (1:ℂ)))
    (hT (Pi.single x 1))
  simp only [LinearMap.comp_apply, diagOp_single, Pi.single_eq_same,
    one_mul] at h
  -- `h : T e_x = diagOp δ_x (T e_x)`; the right side is the coordinate
  -- projection onto the ray at `x`
  ext j
  have hj := congrArg (fun f : ι →₀ ℂ => f j) h
  simp only [diagOp_apply] at hj
  rcases eq_or_ne j x with rfl | hjx
  · rw [Finsupp.single_eq_same]
  · rw [Pi.single_eq_of_ne hjx, zero_mul] at hj
    rw [Finsupp.single_apply, if_neg (fun hxj => hjx hxj.symm)]
    exact hj

/-- **Definition `def:finite-propagation`**: an operator has propagation
`≤ r` when its matrix coefficient `⟨e_y, T e_x⟩` vanishes whenever the
distance from `x` to `y` exceeds `r`. -/
def HasPropagation (dist : ι → ι → ℕ)
    (T : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ)) (r : ℕ) : Prop :=
  ∀ x y : ι, r < dist x y → (T (Finsupp.single x 1)) y = 0

/-- Diagonal multipliers have propagation `0`
(Definition `def:finite-propagation`). -/
theorem diagOp_hasPropagation_zero (dist : ι → ι → ℕ)
    (hdist : ∀ x, dist x x = 0) (d : ι → ℂ) :
    HasPropagation dist (diagOp d) 0 := by
  intro x y h
  rw [diagOp_apply]
  have hne : x ≠ y := by
    intro hxy
    subst hxy
    rw [hdist x] at h
    omega
  simp [Finsupp.single_apply, hne]

/-- Lifted shifts along distance-`≤ 1` transitions have propagation `1`
(Definition `def:finite-propagation`: the generators of the
finite-propagation renewal algebra). -/
theorem shiftOp_hasPropagation_one (dist : ι → ι → ℕ) (s : ι → ι)
    (hs : ∀ x, dist x (s x) ≤ 1) :
    HasPropagation dist (shiftOp s) 1 := by
  intro x y h
  rw [shiftOp_single]
  have hne : s x ≠ y := by
    intro he
    subst he
    exact absurd (hs x) (by omega)
  simp [Finsupp.single_apply, hne]

/-- **Proposition `prop:joint-finite-propagation` (core)**: propagation
is subadditive under composition — if `T` propagates at speed `r` and
`U` at speed `s`, the composite `T ∘ U` propagates at speed `r + s`.
Expanding `U e_x` over its (finite) support, every matrix element of
the composite from `x` to `y` with `dist x y > r + s` factors through
an intermediate site `z` that is either too far from `x` for `U` or too
far from `y` for `T`, by the triangle inequality. -/
theorem hasPropagation_comp (dist : ι → ι → ℕ)
    (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {T U : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ)} {r s : ℕ}
    (hT : HasPropagation dist T r) (hU : HasPropagation dist U s) :
    HasPropagation dist (T ∘ₗ U) (r + s) := by
  intro x y h
  rw [LinearMap.comp_apply]
  have hexp : U (Finsupp.single x 1)
      = ∑ z ∈ (U (Finsupp.single x 1)).support,
          Finsupp.single z ((U (Finsupp.single x 1)) z) := by
    conv_lhs => rw [← Finsupp.sum_single (U (Finsupp.single x 1))]
    rfl
  rw [hexp, map_sum, Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro z _
  have hsingle : Finsupp.single z ((U (Finsupp.single x 1)) z)
      = ((U (Finsupp.single x 1)) z) • Finsupp.single z (1 : ℂ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rcases le_or_gt (dist x z) s with hxz | hxz
  · have hzy : r < dist z y := by
      have := htri x z y
      omega
    rw [hT z y hzy, mul_zero]
  · rw [hU x z hxz, zero_mul]

/-- **Lemma `lem:constant-dirac-kernel` (causal-cone core)**: powers of
a finite-propagation operator propagate linearly — `T^n` has
propagation `n·r`, so the discrete evolution kernel is supported in
the causal cone `dist x y ≤ n·r`. -/
theorem hasPropagation_pow (dist : ι → ι → ℕ)
    (hdist0 : ∀ x, dist x x = 0)
    (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {T : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ)} {r : ℕ}
    (hT : HasPropagation dist T r) (n : ℕ) :
    HasPropagation dist (T ^ n) (n * r) := by
  induction n with
  | zero =>
    intro x y hxy
    have hne : x ≠ y := by
      intro he
      subst he
      rw [hdist0 x] at hxy
      omega
    rw [pow_zero]
    simp [Module.End.one_apply, Finsupp.single_apply, hne]
  | succ n ih =>
    have hcomp := hasPropagation_comp dist htri ih hT
    rw [show (n + 1) * r = n * r + r from by ring, pow_succ,
      Module.End.mul_eq_comp]
    exact hcomp

/-- **Theorem `thm:constant-inner-characterization` (transfer core)**:
a nonzero kernel entry survives compression by the diagonal indicator
projections — if `⟨e_y, T e_x⟩ ≠ 0` with `x ∈ Q`, `y ∈ P`, then the
compressed operator `1_P T 1_Q` is nonzero. -/
theorem compressed_nonzero (T : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ))
    (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    {x y : ι} (hx : Q x) (hy : P y)
    (hne : (T (Finsupp.single x 1)) y ≠ 0) :
    diagOp (fun z => if P z then (1:ℂ) else 0) ∘ₗ T ∘ₗ
      diagOp (fun z => if Q z then (1:ℂ) else 0) ≠ 0 := by
  intro hzero
  apply hne
  have h := congrArg (fun A : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) =>
    (A (Finsupp.single x 1)) y) hzero
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero,
    Pi.zero_apply] at h
  rw [diagOp_single, if_pos hx, one_mul] at h
  rw [diagOp_apply, if_pos hy, one_mul] at h
  exact h

/-- **Theorem `thm:reconstruction` (shift intertwining core)**: if the
basis bijection `φ` intertwines the lifted shifts `S` and `S'` on
basis vectors, the underlying transition maps are conjugate:
`φ(s·x) = s'·φ(x)` — the descended map is a graph isomorphism. -/
theorem shift_conjugation {ι' : Type*} [DecidableEq ι'] (φ : ι ≃ ι')
    (s : ι → ι) (s' : ι' → ι')
    (h : ∀ x : ι, Finsupp.mapDomain φ (shiftOp s (Finsupp.single x 1))
      = shiftOp s' (Finsupp.mapDomain φ (Finsupp.single x (1:ℂ)))) :
    ∀ x, φ (s x) = s' (φ x) := by
  intro x
  have hx := h x
  rw [shiftOp_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    shiftOp_single] at hx
  by_contra hne
  have hval := congrArg (fun f : ι' →₀ ℂ => f (φ (s x))) hx
  simp only [Finsupp.single_eq_same, Finsupp.single_apply] at hval
  rw [if_neg (fun hh => hne hh.symm)] at hval
  exact one_ne_zero hval

/-- **Theorem `thm:reconstruction` (grading core)**: if the basis
bijection `φ` intertwines the diagonal length operators, the gradings
correspond: `Λ(x) = Λ'(φ(x))`. -/
theorem grading_conjugation {ι' : Type*} [DecidableEq ι'] (φ : ι ≃ ι')
    (Λ : ι → ℂ) (Λ' : ι' → ℂ)
    (h : ∀ x : ι, Finsupp.mapDomain φ (diagOp Λ (Finsupp.single x 1))
      = diagOp Λ' (Finsupp.mapDomain φ (Finsupp.single x (1:ℂ)))) :
    ∀ x, Λ x = Λ' (φ x) := by
  intro x
  have hx := h x
  rw [diagOp_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    diagOp_single, mul_one, mul_one] at hx
  have hval := congrArg (fun f : ι' →₀ ℂ => f (φ x)) hx
  simpa only [Finsupp.single_eq_same] using hval

end NCG
