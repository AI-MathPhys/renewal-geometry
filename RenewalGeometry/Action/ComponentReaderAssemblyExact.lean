/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.SobolevReaderCriterionExact

/-!
# Assembly of full-reader bounds from component certificates
  (`prop:component-reader`, Einstein–SM action closure)

The reader tail is `τ_{h,m}(K;u) = Σ_{ℓ∈Λ, |ℓ|_∞>K} (1+|ℓ|₁/K)^m ‖û(ℓ)‖`
(`SobolevReader.tail` of `Action/SobolevReaderCriterionExact.lean`).  The
physical reader is a finite tuple of blocks `u = (u^{(b)})_{b ∈ β}` (geometric,
gauge and matter components), block `b` taking values in a normed space `F b`.

* `componentReader_tail_le_sum` — if `‖û(ℓ)‖ ≤ κ Σ_b ‖û^{(b)}(ℓ)‖` (the fixed
  norm-equivalence constant `κ` of the component norms), then
  `τ(u) ≤ κ Σ_b τ(u^{(b)})` (nonnegative tail weights);
* `componentReader_sum_le` — Cauchy–Schwarz in the finite block index:
  `Σ_b (t_b + c_b √V_b) ≤ Σ_b t_b + (Σ_b c_b²)^{1/2} (Σ_b V_b)^{1/2}`;
* `componentReader_assembly` — `eq:component-reader` up to the equivalence
  constant: `τ(u) ≤ κ (Σ_b t_b + (Σ_b c_b²)^{1/2} √V)`, `V = Σ_b V_b`;
* `componentReader_assembly_euclidean` — for the Euclidean block norm
  (`PiLp 2 F`, the norm of the tuple is `(Σ_b ‖x_b‖²)^{1/2}`) the constant is
  `κ = 1`, which is `eq:component-reader` verbatim.

Scoped hypothesis disclosed: the block budgets satisfy `V_b ≥ 0` (they are
energies); the block constants `c_b` may have any sign.  The clauses about
`S(U(3)×U(2))` Lie-algebra components and gauge identification are
commentary (the proposition "neither chooses those gauges nor establishes any
missing component estimate") and are not formalized.
-/

open scoped BigOperators

namespace RenewalGeometry
namespace SobolevReader

variable {β : Type*} [Fintype β] {F : β → Type*} [∀ b, NormedAddCommGroup (F b)]
  [∀ b, NormedSpace ℝ (F b)]

/-- The tail weights `(1+|ℓ|₁/K)^m` are nonnegative. -/
theorem componentReader_weight_nonneg (j K : ℕ) (ℓ : Mode) : 0 ≤ (1 + l1 ℓ / K) ^ j := by
  have := l1_nonneg ℓ
  positivity

/-- `prop:component-reader`, first step: if the coefficient norm of the tuple is
at most `κ` times the sum of the block norms, then `τ(u) ≤ κ Σ_b τ(u^{(b)})`. -/
theorem componentReader_tail_le_sum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Λ : Finset Mode) (j K : ℕ) (u : Mode → G) (ub : ∀ b, Mode → F b) {κ : ℝ}
    (hnorm : ∀ ℓ, ‖u ℓ‖ ≤ κ * ∑ b, ‖ub b ℓ‖) :
    tail Λ j K u ≤ κ * ∑ b, tail Λ j K (ub b) := by
  unfold tail
  calc ∑ ℓ ∈ Λ.filter (fun ℓ => K < linf ℓ), (1 + l1 ℓ / K) ^ j * ‖u ℓ‖
      ≤ ∑ ℓ ∈ Λ.filter (fun ℓ => K < linf ℓ), (1 + l1 ℓ / K) ^ j * (κ * ∑ b, ‖ub b ℓ‖) :=
        Finset.sum_le_sum fun ℓ _ =>
          mul_le_mul_of_nonneg_left (hnorm ℓ) (componentReader_weight_nonneg j K ℓ)
    _ = κ * ∑ b, ∑ ℓ ∈ Λ.filter (fun ℓ => K < linf ℓ), (1 + l1 ℓ / K) ^ j * ‖ub b ℓ‖ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun ℓ _ => by ring

/-- `prop:component-reader`, Cauchy–Schwarz step: for `V_b ≥ 0`,
`Σ_b (t_b + c_b √V_b) ≤ Σ_b t_b + (Σ_b c_b²)^{1/2} (Σ_b V_b)^{1/2}`. -/
theorem componentReader_sum_le (t c V : β → ℝ) (hV : ∀ b, 0 ≤ V b) :
    ∑ b, (t b + c b * Real.sqrt (V b)) ≤
      ∑ b, t b + Real.sqrt (∑ b, c b ^ 2) * Real.sqrt (∑ b, V b) := by
  rw [Finset.sum_add_distrib]
  refine add_le_add le_rfl ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (fun b => Real.sqrt (V b))
  have hV2 : ∑ b, Real.sqrt (V b) ^ 2 = ∑ b, V b :=
    Finset.sum_congr rfl fun b _ => Real.sq_sqrt (hV b)
  rw [hV2] at hcs
  calc ∑ b, c b * Real.sqrt (V b) ≤ |∑ b, c b * Real.sqrt (V b)| := le_abs_self _
    _ = Real.sqrt ((∑ b, c b * Real.sqrt (V b)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ b, c b ^ 2) * ∑ b, V b) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∑ b, c b ^ 2) * Real.sqrt (∑ b, V b) :=
        Real.sqrt_mul (Finset.sum_nonneg fun b _ => sq_nonneg (c b)) _

/-- `prop:component-reader`, `eq:component-reader` up to the fixed equivalence
constant `κ` of the component norms: if `‖û(ℓ)‖ ≤ κ Σ_b ‖û^{(b)}(ℓ)‖` and
`τ_{h,m}(K;u^{(b)}) ≤ t_b + c_b √V_b` with `V_b ≥ 0`, `V = Σ_b V_b`, then
`τ_{h,m}(K;u) ≤ κ (Σ_b t_b + (Σ_b c_b²)^{1/2} √V)`. -/
theorem componentReader_assembly {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Λ : Finset Mode) (j K : ℕ) (u : Mode → G) (ub : ∀ b, Mode → F b) {κ : ℝ}
    (hκ : 0 ≤ κ) (hnorm : ∀ ℓ, ‖u ℓ‖ ≤ κ * ∑ b, ‖ub b ℓ‖) (t c V : β → ℝ)
    (hV : ∀ b, 0 ≤ V b) (hcomp : ∀ b, tail Λ j K (ub b) ≤ t b + c b * Real.sqrt (V b)) :
    tail Λ j K u ≤
      κ * (∑ b, t b + Real.sqrt (∑ b, c b ^ 2) * Real.sqrt (∑ b, V b)) := by
  refine (componentReader_tail_le_sum Λ j K u ub hnorm).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hκ
  exact (Finset.sum_le_sum fun b _ => hcomp b).trans (componentReader_sum_le t c V hV)

/-- The Euclidean norm of a tuple is at most the sum of its block norms. -/
theorem componentReader_piLp_norm_le (x : PiLp 2 F) : ‖x‖ ≤ ∑ b, ‖x b‖ := by
  rw [PiLp.norm_eq_of_L2]
  have hs : 0 ≤ ∑ b, ‖x b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  calc Real.sqrt (∑ b, ‖x b‖ ^ 2) ≤ Real.sqrt ((∑ b, ‖x b‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun b _ => norm_nonneg _)
    _ = ∑ b, ‖x b‖ := Real.sqrt_sq hs

/-- `prop:component-reader`, `eq:component-reader` for the Euclidean block norm
(`κ = 1`): for a tuple-valued reader `u : Mode → PiLp 2 F` with component
certificates `τ_{h,m}(K;u^{(b)}) ≤ t_b + c_b √V_b` (`V_b ≥ 0`, `V = Σ_b V_b`),
`τ_{h,m}(K;u) ≤ Σ_b t_b + (Σ_b c_b²)^{1/2} √V`. -/
theorem componentReader_assembly_euclidean (Λ : Finset Mode) (j K : ℕ) (u : Mode → PiLp 2 F)
    (t c V : β → ℝ) (hV : ∀ b, 0 ≤ V b)
    (hcomp : ∀ b, tail Λ j K (fun ℓ => u ℓ b) ≤ t b + c b * Real.sqrt (V b)) :
    tail Λ j K u ≤ ∑ b, t b + Real.sqrt (∑ b, c b ^ 2) * Real.sqrt (∑ b, V b) := by
  have h := componentReader_assembly Λ j K u (fun b ℓ => u ℓ b) zero_le_one
    (fun ℓ => by rw [one_mul]; exact componentReader_piLp_norm_le (u ℓ)) t c V hV hcomp
  rwa [one_mul] at h

end SobolevReader
end RenewalGeometry
