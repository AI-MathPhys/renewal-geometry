/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PrimitiveWeight
import NCG.Grand.SourceInfluenceExtremizerAttainmentExact

/-!
# Spectral tail bound from Choi purity

For nonnegative weights of total mass `d`, their largest weight is at least
the quadratic mass divided by `d`.  Equivalently, the mass discarded after
keeping a largest weight is bounded by

`(d^2 - sum_i w_i^2) / d`.

The matrix specialization identifies these weights with the eigenvalues of a
positive Choi matrix and the quadratic mass with `Re Tr(J^2)`.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace ChoiPuritySpectralTail

open Upstream.PrimitiveWeight

/-- Elementary finite purity bound for an explicitly chosen largest weight. -/
theorem finite_purity_tail_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (k : ι) {d : ℝ}
    (hd : 0 < d) (hw : ∀ i, 0 ≤ w i)
    (hk : ∀ i, w i ≤ w k) (hsum : ∑ i, w i = d) :
    d - w k ≤ (d ^ 2 - ∑ i, (w i) ^ 2) / d := by
  have hsquare : ∑ i, (w i) ^ 2 ≤ w k * d := by
    calc
      ∑ i, (w i) ^ 2 ≤ ∑ i, w k * w i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hk i) (hw i)
      _ = w k * ∑ i, w i := by rw [Finset.mul_sum]
      _ = w k * d := by rw [hsum]
  rw [le_div_iff₀ hd]
  nlinarith

variable {m : ℕ}

/-- Matrix form: for a positive matrix of real trace `d`, a largest
eigenvalue leaves trace mass at most the normalized purity defect. -/
theorem psd_purity_tail_bound
    {J : Matrix (Fin m) (Fin m) ℂ} (hJ : J.PosSemidef)
    (k : Fin m) {d : ℝ} (hd : 0 < d)
    (hk : ∀ i, hJ.1.eigenvalues i ≤ hJ.1.eigenvalues k)
    (htrace : J.trace.re = d) :
    d - hJ.1.eigenvalues k ≤
      (d ^ 2 - (J * J).trace.re) / d := by
  let hH : J.IsHermitian := hJ.1
  change (∀ i, hH.eigenvalues i ≤ hH.eigenvalues k) at hk
  change d - hH.eigenvalues k ≤ (d ^ 2 - (J * J).trace.re) / d
  have hsum : ∑ i, hH.eigenvalues i = d := by
    rw [← htrace]
    rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_re _).symm
  have hsq : J * J = hH.cfc (fun x => x * x) := by
    calc
      J * J = hH.cfc id * hH.cfc id := by
        rw [cfc_id' hH]
      _ = hH.cfc (fun x => id x * id x) := cfc_mul hH id id
      _ = hH.cfc (fun x => x * x) := by rfl
  have hpure : (J * J).trace.re =
      ∑ i, (hH.eigenvalues i) ^ 2 := by
    rw [hsq, cfc_trace]
    change (∑ i, hH.eigenvalues i * hH.eigenvalues i) =
      ∑ i, hH.eigenvalues i ^ 2
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hpure]
  have hw : ∀ i, 0 ≤ hH.eigenvalues i := by
    intro i
    exact hJ.eigenvalues_nonneg i
  exact finite_purity_tail_bound hH.eigenvalues k hd hw hk hsum

/-- A positive finite matrix has a largest eigenvalue satisfying the purity
tail bound, with no maximizing index supplied by the caller. -/
theorem exists_purity_controlling_eigenvalue
    {J : Matrix (Fin m) (Fin m) ℂ} [Nonempty (Fin m)]
    (hJ : J.PosSemidef) {d : ℝ} (hd : 0 < d)
    (htrace : J.trace.re = d) :
    ∃ k : Fin m,
      (∀ i, hJ.1.eigenvalues i ≤ hJ.1.eigenvalues k) ∧
      d - hJ.1.eigenvalues k ≤
        (d ^ 2 - (J * J).trace.re) / d := by
  obtain ⟨k, hk⟩ :=
    SourceInfluenceAttainment.exists_max_eigenindex hJ.1
  exact ⟨k, hk, psd_purity_tail_bound hJ k hd hk htrace⟩

end ChoiPuritySpectralTail
end NCG
