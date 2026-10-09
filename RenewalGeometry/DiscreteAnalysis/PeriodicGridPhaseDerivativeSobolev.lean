/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSobolevSpace
import RenewalGeometry.DiscreteAnalysis.OddPhaseDerivativeReal
import RenewalGeometry.Gravity.InitialConstraintLinearRange

/-!
# The odd phase derivative and the lattice shifts on the grid Sobolev spaces
  (infrastructure for `lem:supp-initial-calculus`: "every spatial load has one phase derivative …
  the output loses at most the declared Sobolev orders"; emergent-spacetime manuscript)

On the periodic grid `(ℤ/N)³` with the grid Sobolev norms `‖·‖_{r,h}` (`sobNorm`, built from the
forward differences `D_i⁺`):

* `sobSq_delta`: the odd phase derivative `δ_i` (the Fourier multiplier `iκ_i(k)`,
  `κ_i(k) = 2h⁻¹ sin(πhk_i)`, `eq:supp-initial-phase-derivative`) has the same squared Sobolev
  norm as the forward difference: `‖δ_i u‖_{r,h} = ‖D_i⁺u‖_{r,h}` (`|κ_i| = |symbol of D_i⁺|`);
* `sobNorm_delta_le`: hence `‖δ_i u‖_{r,h} ≤ ‖u‖_{r+1,h}`, **uniformly in `N`**;
* `GridH.pdL` (odd `N`): the real phase derivative `pd i` as a continuous linear map
  `H^{r+1}_h → H^r_h` with `‖pdL‖ ≤ 1` (`GridH.norm_pdL_le`);
* `sobSq_S`, `GridH.shiftL`: the lattice translation `u ↦ u(· + e_i)` preserves `‖·‖_{r,h}`;
  as a continuous linear map `H^r_h → H^r_h` it has norm `≤ 1` (`GridH.norm_shiftL_le`).
-/

open Finset

namespace RenewalGeometry.PhaseDerivSobolev

open PeriodicGridSobolev LatticeTorusPlancherel InitialConstraintLinearRange

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-- `‖δ_i u‖²_{r,h} = ‖D_i⁺u‖²_{r,h}`: the odd phase symbol and the forward-difference symbol
have the same modulus. -/
theorem sobSq_delta (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    sobSq r (delta i u) = sobSq r (Dp i u) := by
  rw [sobSq_eq_weight, sobSq_eq_weight]
  refine sum_congr rfl fun k _ => ?_
  have h1 : dft (delta i u) k = Complex.I * (kap i k : ℂ) * dft u k := dftL_delta i u k
  have h2 : dft (Dp i u) k = sym i k * dft u k := isMult_Dp i u k
  rw [h1, h2, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_kap_eq, one_mul]

theorem deg_single (i : Fin 3) : deg (Pi.single i 1 : Fin 3 → ℕ) = 1 := by
  fin_cases i <;> simp [deg]

/-- **The phase derivative loses exactly one Sobolev order, uniformly in the cutoff**:
`‖δ_i u‖_{r,h} ≤ ‖u‖_{r+1,h}`. -/
theorem sobNorm_delta_le (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    sobNorm r (delta i u) ≤ sobNorm (r + 1) u := by
  unfold sobNorm
  refine Real.sqrt_le_sqrt ?_
  rw [sobSq_delta]
  have h := sobSq_Dα_le (N := N) (β := Pi.single i 1) (s := r) (r := r + 1)
    (by rw [deg_single]; omega) u
  rwa [Dα_single] at h

/-- Lattice translations preserve the grid Sobolev norms. -/
theorem sobSq_S (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) : sobSq r (S i u) = sobSq r u := by
  rw [sobSq_eq_weight, sobSq_eq_weight]
  refine sum_congr rfl fun k _ => ?_
  rw [isMult_S i u k, norm_mul, norm_chi, one_mul]

namespace GridH

open OddPhaseDerivativeReal

/-- The real phase derivative as a continuous linear map `H^{r+1}_h → H^r_h` (odd `N`). -/
def pdL (hN : Odd N) (r : ℕ) (i : Fin 3) : PeriodicGridSobolev.GridH N (r + 1) →L[ℝ]
    PeriodicGridSobolev.GridH N r :=
  PeriodicGridSobolev.GridH.ofBound (pd i) 1 fun u => by
    rw [PeriodicGridSobolev.GridH.norm_def, PeriodicGridSobolev.GridH.norm_def, one_mul]
    have e : PeriodicGridSobolev.GridH.cxv (PeriodicGridSobolev.GridH.mk (r := r)
        (pd i (PeriodicGridSobolev.GridH.val u))) =
        delta i (PeriodicGridSobolev.GridH.cxv u) := by
      have := ofReal_pd hN i (PeriodicGridSobolev.GridH.val u)
      exact this
    rw [e]
    exact sobNorm_delta_le r i _

@[simp] theorem pdL_val (hN : Odd N) (r : ℕ) (i : Fin 3)
    (u : PeriodicGridSobolev.GridH N (r + 1)) :
    PeriodicGridSobolev.GridH.val (pdL hN r i u) = pd i (PeriodicGridSobolev.GridH.val u) := rfl

/-- `‖δ_i‖_{H^{r+1}_h → H^r_h} ≤ 1` for every odd `N`. -/
theorem norm_pdL_le (hN : Odd N) (r : ℕ) (i : Fin 3) : ‖pdL hN r i‖ ≤ 1 :=
  PeriodicGridSobolev.GridH.norm_ofBound_le _ zero_le_one _

/-- The lattice translation `u ↦ u(· + e_i)` as a continuous linear map `H^r_h → H^r_h`. -/
def shiftL (r : ℕ) (i : Fin 3) : PeriodicGridSobolev.GridH N r →L[ℝ]
    PeriodicGridSobolev.GridH N r :=
  PeriodicGridSobolev.GridH.ofBound (LinearMap.funLeft ℝ ℝ (fun x : Grid N => x + unit i)) 1
    fun u => by
      rw [PeriodicGridSobolev.GridH.norm_def, PeriodicGridSobolev.GridH.norm_def, one_mul]
      have e : PeriodicGridSobolev.GridH.cxv (PeriodicGridSobolev.GridH.mk (r := r)
          (LinearMap.funLeft ℝ ℝ (fun x : Grid N => x + unit i) (PeriodicGridSobolev.GridH.val u))) =
          S i (PeriodicGridSobolev.GridH.cxv u) := rfl
      rw [e]
      unfold sobNorm
      rw [sobSq_S]

/-- Lattice translations are contractions (in fact isometries) of `H^r_h`. -/
theorem norm_shiftL_le (r : ℕ) (i : Fin 3) : ‖shiftL (N := N) r i‖ ≤ 1 :=
  PeriodicGridSobolev.GridH.norm_ofBound_le _ zero_le_one _

end GridH

end

end RenewalGeometry.PhaseDerivSobolev
