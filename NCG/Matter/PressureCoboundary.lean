/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PressureGauge

/-!
# Coboundary tilts have flat pressure
  (`thm:linear-pressure-cancellation-nogo-consolidated`,
   SM_emergence)

If the centered scalar record is a predictive coboundary
`f(x, y) = g(y) - g(x)`, the tilted kernel
`Q_χ(x,y) = e^{χ(g(y)-g(x))}Q(x,y)` is a positive diagonal
conjugation of `Q`, so its Perron growth rate — hence the scaled
pressure — is independent of `χ`:

* `coboundary_tilt_pressure_invariant` — `pRad Q_χ = pRad Q` for
  every `χ` (via `pRad_diag_conj`);
* `flat_pressure_cumulants_vanish` — a constant pressure has all
  derivatives (connected cumulants) zero, including the quartic.

Hence ordinary connected centering cannot set `m_H² = 0` while
retaining a nonzero connected Higgs quartic.  The equivalence
`vanishing asymptotic variance ↔ coboundary` (the Markov CLT
degeneracy criterion) is the declared probabilistic input.
-/

namespace NCG

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- `thm:linear-pressure-cancellation-nogo-consolidated` (coboundary
tilt): tilting by a predictive coboundary is a positive diagonal
conjugation, so the Perron growth rate is `χ`-independent. -/
theorem coboundary_tilt_pressure_invariant {Q : Matrix V V ℝ}
    (hQ : EntryNonneg Q) (hw : HasDiagWitness Q) (g : V → ℝ)
    (chi : ℝ) :
    pRad (Matrix.of fun x y =>
      Real.exp (chi * (g y - g x)) * Q x y) = pRad Q := by
  have h := pRad_diag_conj hQ hw
    (fun x => Real.exp (-(chi * g x))) (fun x => Real.exp_pos _)
  rw [← h]
  congr 1
  ext x y
  rw [diag_conj_entry]
  rw [show (Real.exp (-(chi * g y)))⁻¹ = Real.exp (chi * g y) from by
    rw [← Real.exp_neg, neg_neg]]
  rw [Matrix.of_apply, mul_right_comm, ← Real.exp_add]
  congr 2
  ring

/-- `thm:linear-pressure-cancellation-nogo-consolidated` (cumulant
collapse): a `χ`-independent pressure has every connected cumulant
zero — including the quartic. -/
theorem flat_pressure_cumulants_vanish {L : ℝ → ℝ} {c : ℝ}
    (hL : ∀ x, L x = c) {n : ℕ} (hn : n ≠ 0) :
    iteratedDeriv n L 0 = 0 := by
  have hzero : ∀ k : ℕ, iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) 0 = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ']
      rw [show deriv (fun _ : ℝ => (0 : ℝ)) = fun _ : ℝ => (0 : ℝ) from
        funext fun x => deriv_const x 0]
      exact ih
  have hfun : L = fun _ => c := funext hL
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hfun, iteratedDeriv_succ']
  rw [show deriv (fun _ : ℝ => c) = fun _ : ℝ => (0 : ℝ) from
    funext fun x => deriv_const x c]
  exact hzero m

end NCG
