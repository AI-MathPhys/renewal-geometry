/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Diagonal operators and shifts on the predictive module

The positive predictive spectral triple of the manuscript
(Theorem `thm:triple`) lives on `ℓ²(𝒲_CP)`, with

* the **length Dirac** `D_CP e_[w] = Λ_min([w]) e_[w]`, a diagonal operator,
* the **descended shifts** `Ŝ_σ e_[w] = e_[σw]`.

This file develops the *algebraic core* of that model on the dense submodule
of finitely supported vectors `ι →₀ ℂ`: diagonal operators `diagOp d`,
shifts `shiftOp s` along a map `s : ι → ι`, and their commutation relations.
The analytic layer (boundedness under finite fibres, compact resolvent,
summability — Theorem `thm:fibre-dichotomy`, Theorem `thm:triple`,
Theorem `thm:weyl-law`) is a downstream target on `ℓ²`.

## Main results

* `diagOp_comm_shiftOp_single` — the commutator formula
  `[D, Ŝ] e_i = (d(s i) − d(i)) e_{s i}` behind the bounded-commutator
  condition of Theorem `thm:triple`;
* `clock_scaling` — the graded clock-scaling identity
  `e^{βN} ∘ Ŝ = e^β · (Ŝ ∘ e^{βN})` for unit-increment shifts
  (Lemma `lem:clock-scaling`), the renewal incarnation of the
  Connes–Rovelli thermal-time flow.
-/

namespace NCG

open Finsupp

variable {ι : Type*}

/-- The **diagonal operator** with symbol `d : ι → ℂ` on finitely supported
vectors: `diagOp d (e_i) = d i • e_i`.  This is the algebraic model of the
length Dirac `D_CP` (with `d = Λ_min`) and of the modular weight `e^{βN}`. -/
noncomputable def diagOp (d : ι → ℂ) : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) :=
  Finsupp.lsum ℂ fun i => d i • Finsupp.lsingle i

@[simp]
theorem diagOp_single (d : ι → ℂ) (i : ι) (c : ℂ) :
    diagOp d (Finsupp.single i c) = Finsupp.single i (d i * c) := by
  simp [diagOp, Finsupp.smul_single, mul_comm]

/-- The **shift operator** along a map `s : ι → ι` on finitely supported
vectors: `shiftOp s (e_i) = e_{s i}`.  With `ι = 𝒲_CP` and `s = (σ · )` this
is the descended shift `Ŝ_σ` of Lemma `lem:shift-congruence`. -/
noncomputable def shiftOp (s : ι → ι) : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ s

@[simp]
theorem shiftOp_single (s : ι → ι) (i : ι) (c : ℂ) :
    shiftOp s (Finsupp.single i c) = Finsupp.single (s i) c := by
  simp [shiftOp, Finsupp.mapDomain_single]

/-- **Commutator formula** for the length Dirac against a shift
(Theorem `thm:triple`): on basis vectors,
`[diagOp d, shiftOp s] e_i = (d (s i) − d i) • e_{s i}`.
Bounded length increments `|d (s i) − d i| ≤ C` are exactly what make this
commutator bounded on `ℓ²`, which is the Lipschitz condition of the
predictive spectral triple (Assumption `ass:fibres`). -/
theorem diagOp_comm_shiftOp_single (d : ι → ℂ) (s : ι → ι) (i : ι) (c : ℂ) :
    (diagOp d ∘ₗ shiftOp s - shiftOp s ∘ₗ diagOp d) (Finsupp.single i c)
      = (d (s i) - d i) • Finsupp.single (s i) c := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, shiftOp_single,
    diagOp_single, Finsupp.smul_single, smul_eq_mul, sub_mul,
    Finsupp.single_sub]

/-- **Lemma `lem:clock-scaling`** (graded clock scaling): if the shift `s`
raises the renewal clock `N` by exactly one, then the modular weight
`Δ = e^{βN}` satisfies

`Δ ∘ Ŝ = e^β • (Ŝ ∘ Δ)`,

i.e. `Ad(e^{βN})(Ŝ) = e^β Ŝ` after conjugation.  The modular automorphism
scales every elementary reset by the single constant `e^β` — the renewal
incarnation of the Connes–Rovelli thermal-time flow. -/
theorem clock_scaling (N : ι → ℝ) (s : ι → ι) (hstep : ∀ i, N (s i) = N i + 1)
    (β : ℝ) :
    diagOp (fun i => (Real.exp (β * N i) : ℂ)) ∘ₗ shiftOp s
      = (Real.exp β : ℂ) • (shiftOp s ∘ₗ
          diagOp fun i => (Real.exp (β * N i) : ℂ)) := by
  apply Finsupp.lhom_ext
  intro i c
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, shiftOp_single,
    diagOp_single, Finsupp.smul_single, smul_eq_mul]
  congr 1
  have hexp : Real.exp (β * N (s i)) = Real.exp β * Real.exp (β * N i) := by
    rw [hstep i, mul_add, mul_one, add_comm, Real.exp_add]
  rw [hexp]
  push_cast
  ring

/-- Diagonal operators commute with each other. -/
theorem diagOp_comm (d d' : ι → ℂ) :
    diagOp d ∘ₗ diagOp d' = diagOp d' ∘ₗ diagOp d := by
  apply Finsupp.lhom_ext
  intro i c
  simp only [LinearMap.comp_apply, diagOp_single]
  ring_nf

end NCG
