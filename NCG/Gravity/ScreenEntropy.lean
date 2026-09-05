/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Screen entropy: memory loss, strip rate, and the area law
  (GR_emergence, screen cluster)

The quantitative skeleton of the renewal-screen area-law cluster:

* `memory_loss_iterate` (`lem:boundary-memory-loss`): iterating a
  trace-norm `q`-contraction (the dual renewal channel `(ℰ*)^r`,
  with `q = e^{-1/ξ}` from primitivity) separates any two endpoint
  memories by at most `q^r` times their initial distance — the
  boundary factor is the sum over `|∂Σ|` endpoints;
* `increment_rate_expansion` (`lem:strip-entropy-rate`): a sequence
  whose increments converge to a rate `η` at speed `C q^{n+1}`
  satisfies `S_n = n η + b + O(qⁿ)` with the explicit strip constant
  `b = S 0 + Σ (increments - η)` and remainder `≤ C q^{n+1}/(1-q)`;
* `screen_area_law_assembly` (`thm:renewal-screen-area-law`): the
  triangle assembly of the extensive strip term, the boundary
  counterterm, the collar memory error `O(|∂Σ| e^{-r/ξ})`, and the
  area regularization `O(ε|∂Σ|)` into the boundary-local area law
  for the renormalized split entropy `S - B_r`.

The von Neumann entropy inputs (Alicki–Fannes continuity of the
conditional increments, complete positivity of later emissions) are
the disclosed interface hypotheses — they supply the contraction and
increment-convergence hypotheses below for the concrete renewal
channel.
-/

namespace NCG

/-- `lem:boundary-memory-loss` (contraction core): iterating a
`q`-contraction separates two endpoint memories by at most `q^r`
times their initial trace distance. -/
theorem memory_loss_iterate {X : Type*} [SeminormedAddCommGroup X]
    {Φ : X → X} {q : ℝ} (hq0 : 0 ≤ q)
    (hcontr : ∀ x y, ‖Φ x - Φ y‖ ≤ q * ‖x - y‖) (x y : X) (r : ℕ) :
    ‖Φ^[r] x - Φ^[r] y‖ ≤ q ^ r * ‖x - y‖ := by
  induction r with
  | zero => simp
  | succ n ih =>
      calc ‖Φ^[n + 1] x - Φ^[n + 1] y‖
          = ‖Φ (Φ^[n] x) - Φ (Φ^[n] y)‖ := by
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      _ ≤ q * ‖Φ^[n] x - Φ^[n] y‖ := hcontr _ _
      _ ≤ q * (q ^ n * ‖x - y‖) := by
            apply mul_le_mul_of_nonneg_left ih hq0
      _ = q ^ (n + 1) * ‖x - y‖ := by ring

/-- `lem:strip-entropy-rate` (increment expansion): if the increments
of `S` converge to the rate `η` at geometric speed `C q^{n+1}`, then
`S n = n η + b + O(qⁿ)` with the explicit strip constant
`b = S 0 + Σ (increments - η)`. -/
theorem increment_rate_expansion {S : ℕ → ℝ} {η C q : ℝ}
    (hq0 : 0 ≤ q) (hq : q < 1)
    (hinc : ∀ n : ℕ, |S (n + 1) - S n - η| ≤ C * q ^ (n + 1)) :
    ∃ b : ℝ, ∀ n : ℕ,
      |S n - n * η - b| ≤ C * q ^ (n + 1) / (1 - q) := by
  set d : ℕ → ℝ := fun k => S (k + 1) - S k - η with hd
  have hgsum : Summable (fun k : ℕ => C * q ^ (k + 1)) := by
    have h := (summable_geometric_of_lt_one hq0 hq).mul_left (C * q)
    exact h.congr fun k => by ring
  have hsum : Summable d := by
    apply Summable.of_norm_bounded hgsum
    intro k
    rw [Real.norm_eq_abs]
    exact hinc k
  refine ⟨S 0 + ∑' k, d k, fun n => ?_⟩
  have htel : S n = S 0 + n * η + ∑ k ∈ Finset.range n, d k := by
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ← add_assoc]
        have hSm : S (m + 1) = S m + η + d m := by
          simp only [hd]
          ring
        rw [hSm, ih]
        push_cast
        ring
  have hsplit := hsum.sum_add_tsum_nat_add n
  have hkey : S n - n * η - (S 0 + ∑' k, d k) = -(∑' k, d (k + n)) := by
    rw [htel, ← hsplit]
    ring
  rw [hkey, abs_neg]
  have htail : Summable (fun k => d (k + n)) :=
    (summable_nat_add_iff n).mpr hsum
  have hgtail : Summable (fun k : ℕ => C * q ^ (k + n + 1)) := by
    have h := (summable_geometric_of_lt_one hq0 hq).mul_left
      (C * q ^ (n + 1))
    exact h.congr fun k => by ring
  have habs : |∑' k, d (k + n)| ≤ ∑' k : ℕ, C * q ^ (k + n + 1) := by
    calc |∑' k, d (k + n)| ≤ ∑' k, |d (k + n)| := by
          have habs2 : Summable (fun k => |d (k + n)|) := htail.abs
          have := norm_tsum_le_tsum_norm (f := fun k => d (k + n))
            (by simpa [Real.norm_eq_abs] using habs2)
          simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' k : ℕ, C * q ^ (k + n + 1) := by
          refine Summable.tsum_le_tsum (fun k => ?_) htail.abs hgtail
          simp only [hd]
          exact hinc (k + n)
  have hgeom : ∑' k : ℕ, C * q ^ (k + n + 1)
      = C * q ^ (n + 1) / (1 - q) := by
    have hcongr : ∀ k : ℕ, C * q ^ (k + n + 1)
        = C * q ^ (n + 1) * q ^ k := by
      intro k
      ring
    rw [tsum_congr hcongr, tsum_mul_left,
      tsum_geometric_of_lt_one hq0 hq]
    field_simp
  rw [hgeom] at habs
  exact habs

/-- `thm:renewal-screen-area-law` (assembly): given the summed strip
expansion `|S - η N - B| ≤ c₁|∂Σ|e^{-r/ξ}` (strip rate + boundary
memory loss) and the area regularization `|A - a N| ≤ c₂ ε |∂Σ|`,
the renormalized split entropy `S - B` satisfies the boundary-local
area law with density `η_scr = η/a`. -/
theorem screen_area_law_assembly {S A B N bd η a c1 c2 r ξ ε : ℝ}
    (ha : 0 < a) (hη : 0 ≤ η)
    (hS : |S - η * N - B| ≤ c1 * bd * Real.exp (-(r / ξ)))
    (hA : |A - a * N| ≤ c2 * ε * bd) :
    |S - B - η / a * A| ≤
      c1 * bd * Real.exp (-(r / ξ)) + η / a * (c2 * ε * bd) := by
  have hkey : S - B - η / a * A
      = (S - η * N - B) - η / a * (A - a * N) := by
    field_simp
    ring
  rw [hkey]
  calc |(S - η * N - B) - η / a * (A - a * N)|
      ≤ |S - η * N - B| + |η / a * (A - a * N)| := abs_sub _ _
  _ = |S - η * N - B| + η / a * |A - a * N| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hη ha.le)]
  _ ≤ c1 * bd * Real.exp (-(r / ξ)) + η / a * (c2 * ε * bd) := by
      have := mul_le_mul_of_nonneg_left hA (div_nonneg hη ha.le)
      linarith

end NCG
