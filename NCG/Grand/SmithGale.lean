/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The derived Smith–Gale exact sequence
  (`thm:Smith-Gale-sequence`, `cor:Gale-completeness`,
   Gran-Tensor manuscript)

* `smith_gale_sequence`: the boxed exact sequence
  `0 → 𝓛_A/q𝓛_A → Ker A_q → 𝓒_A[q] → 0`, rendered element-wise
  on integral lifts: `ρ_q`-injectivity (a kernel vector divisible
  by `q` is divisible inside the kernel), the connecting map
  `β_q(x̄) = [y]` for `Ax = q•y` is torsion-valued and independent
  of the lift, exactness at the middle (`β_q(x̄) = 0` iff `x̄` is
  the reduction of an integral kernel vector), and `β_q`
  surjectivity onto the `q`-torsion of the cokernel.
* `gale_completeness`: the reduction of the integral kernel spans
  `Ker A_q` exactly when `𝓒_A[q] = 0`.
* `gale_completeness_all`: completeness for every `q ≠ 0` is
  equivalent to the cokernel being torsion free.

Rendering disclosed: the sequence is stated on lifts (kernel
vectors of the reduction are represented by `x` with `Ax = q•y`),
so the quotient-module packaging of `ρ_q, β_q` is bookkeeping
over the proved clauses; scalars are a general integral domain
with torsion-free target (the manuscript's `ℤ`-lattice map is
the instance); the Smith-invariant reformulation `gcd(dᵢ, q) = 1`
of the corollary is the manuscript's Smith-normal-form
bookkeeping.
-/

namespace NCG

variable {R M N : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.IsTorsionFree R N]

/-- `thm:Smith-Gale-sequence`: the derived exact sequence
`0 → 𝓛_A/q𝓛_A → Ker A_q → 𝓒_A[q] → 0`, element-wise on lifts. -/
theorem smith_gale_sequence (A : M →ₗ[R] N) (q : R) (hq : q ≠ 0) :
    (∀ x ∈ LinearMap.ker A, ∀ w : M, x = q • w
      → w ∈ LinearMap.ker A)
    ∧ (∀ x y, A x = q • y →
        q • (Submodule.Quotient.mk y : N ⧸ LinearMap.range A) = 0)
    ∧ (∀ x x' y y', A x = q • y → A x' = q • y' →
        (∃ w : M, x' - x = q • w) →
        (Submodule.Quotient.mk y : N ⧸ LinearMap.range A)
          = Submodule.Quotient.mk y')
    ∧ (∀ x y, A x = q • y →
        ((Submodule.Quotient.mk y : N ⧸ LinearMap.range A) = 0
          ↔ ∃ l ∈ LinearMap.ker A, ∃ w : M, x - l = q • w))
    ∧ (∀ c : N ⧸ LinearMap.range A, q • c = 0 →
        ∃ x y, A x = q • y
          ∧ (Submodule.Quotient.mk y : N ⧸ LinearMap.range A)
              = c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ρ_q injectivity: q-divisible kernel vectors divide in 𝓛_A
    intro x hx w hw
    rw [LinearMap.mem_ker] at hx ⊢
    have h : q • A w = q • (0 : N) := by
      rw [smul_zero, ← A.map_smul, ← hw]
      exact hx
    exact smul_right_injective N hq h
  · -- β_q lands in the q-torsion of the cokernel
    intro x y hxy
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr ⟨x, hxy⟩
  · -- β_q is independent of the chosen lift
    intro x x' y y' h h' hw'
    obtain ⟨w, hw⟩ := hw'
    have hA : A (x' - x) = A (q • w) := congrArg A hw
    rw [A.map_sub, A.map_smul, h, h'] at hA
    have key : q • (y' - y) = q • A w := by
      rw [smul_sub]
      exact hA
    have h2 : y' - y = A w := smul_right_injective N hq key
    rw [eq_comm, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr ⟨w, h2.symm⟩
  · -- exactness at the middle: Ker β_q = Im ρ_q
    intro x y hxy
    constructor
    · intro h0
      rw [Submodule.Quotient.mk_eq_zero] at h0
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp h0
      refine ⟨x - q • v, ?_, v, ?_⟩
      · rw [LinearMap.mem_ker, A.map_sub, A.map_smul, hv, hxy,
          sub_self]
      · rw [sub_sub_cancel]
    · rintro ⟨l, hl, w, hw⟩
      rw [LinearMap.mem_ker] at hl
      have hA : A (x - l) = A (q • w) := congrArg A hw
      rw [A.map_sub, hl, sub_zero, A.map_smul, hxy] at hA
      have h2 : y = A w := smul_right_injective N hq hA
      rw [Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.mpr ⟨w, h2.symm⟩
  · -- β_q surjectivity onto the q-torsion
    intro c hc
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hc
    exact ⟨x, v, hx, rfl⟩

/-- `cor:Gale-completeness` (fixed `q`): the reduction of the
integral kernel spans `Ker A_q` iff `𝓒_A[q] = 0`. -/
theorem gale_completeness (A : M →ₗ[R] N) (q : R) (hq : q ≠ 0) :
    (∀ x y, A x = q • y →
        ∃ l ∈ LinearMap.ker A, ∃ w : M, x - l = q • w)
    ↔ (∀ c : N ⧸ LinearMap.range A, q • c = 0 → c = 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := smith_gale_sequence A q hq
  constructor
  · intro hspan c hc
    obtain ⟨x, y, hxy, hy⟩ := h5 c hc
    rw [← hy]
    exact (h4 x y hxy).mpr (hspan x y hxy)
  · intro htor x y hxy
    exact (h4 x y hxy).mp (htor _ (h2 x y hxy))

/-- `cor:Gale-completeness` (all `q`): the integral Gale basis is
complete for every modulus iff the cokernel is torsion free. -/
theorem gale_completeness_all (A : M →ₗ[R] N) :
    (∀ q : R, q ≠ 0 → ∀ x y, A x = q • y →
        ∃ l ∈ LinearMap.ker A, ∃ w : M, x - l = q • w)
    ↔ (∀ q : R, q ≠ 0 →
        ∀ c : N ⧸ LinearMap.range A, q • c = 0 → c = 0) := by
  constructor
  · intro h q hq
    exact (gale_completeness A q hq).mp (h q hq)
  · intro h q hq
    exact (gale_completeness A q hq).mpr (h q hq)

end NCG
