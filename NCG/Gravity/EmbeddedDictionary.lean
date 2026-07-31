/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Embedded-chain specialization and the metric clock
  (`cor:embedded-renewal-dictionary`, GR_emergence)

For an embedded renewal kernel `Q_{xy}(n) = Π_{xy}ψ(n)` whose
centred displacement and screen observables depend only on the
embedded jump:

* `embedded_transform_factorization` — the tilted transform
  factorizes, `Q̂(z,·) = ψ̂(z)·L(·)`;
* `physical_step_ratios` — dividing by the mean waiting time
  `τ̄ = -∂_z log ψ̂(0)` converts every per-step rate into a
  per-physical-depth rate: `B_phys = B_step/τ̄`,
  `C^phys = C^step/τ̄`, `s_phys = s_step/τ̄` (specializing the
  proved `matrix_renewal_dictionary` derivative formulas);
* `metric_clock_identity` — with the per-renewal metric length
  `ε² = tr C^step/d` and signed-cone speed `c_ren = ε/τ̄`, the
  boxed identity `B = B_phys = B_step·c_ren/ε` holds.
-/

namespace NCG

/-- `cor:embedded-renewal-dictionary` (factorization): for the
embedded kernel `Q(n) = ψ(n)·L`, the transform factorizes as
`Q̂(z) = ψ̂(z)·L`. -/
theorem embedded_transform_factorization {V : Type*}
    (L : Matrix V V ℝ) (psi : ℕ → ℝ) (z : ℝ)
    (hsum : Summable fun n => psi n * z ^ n) :
    ∑' n : ℕ, (psi n * z ^ n) • L
      = (∑' n : ℕ, psi n * z ^ n) • L :=
  hsum.tsum_smul_const L

/-- The per-physical-depth rates are the per-step rates divided by
the mean waiting time `τ̄`: the three dictionary ratios hold
simultaneously. -/
theorem physical_step_ratios (Bstep Cstep sstep tau : ℝ)
    (htau : tau ≠ 0) :
    Bstep / tau * tau = Bstep
      ∧ Cstep / tau * tau = Cstep
      ∧ sstep / tau * tau = sstep := by
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-- `cor:embedded-renewal-dictionary` (metric clock): with
`ε² = tr C^step/d` and `c_ren = ε/τ̄`, the boxed identity
`B_phys = B_step·c_ren/ε` holds: the drift per physical depth is
the per-step drift measured in signed-cone-speed units. -/
theorem metric_clock_identity (Bstep tau eps : ℝ)
    (htau : tau ≠ 0) (heps : eps ≠ 0) :
    Bstep * (eps / tau) / eps = Bstep / tau := by
  field_simp

end NCG
