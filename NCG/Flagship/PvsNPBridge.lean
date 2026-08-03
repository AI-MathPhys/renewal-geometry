/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Ambient record dimension firewall and the complexity bridge
  (`prop:PvsNP-dimension-master`, `thm:PvsNP-bridge-master`,
   flagship manuscript)

* `record_dimension_firewall` / `boolean_record_dimension`:
  representing `m` records (in particular all `2ⁿ` Boolean
  inputs) by orthonormal vectors forces ambient dimension at
  least `m` (resp. `2ⁿ`);
* `foldl_xor_shift` / `parity_fold_iff`: the parity function is
  computed exactly by the linear chain of `xor` gates — one gate
  per input bit — so exponential record dimension coexists with
  linear circuit size and implies no circuit lower bound;
* `Superpoly` and `pvsnp_bridge`: the conditional
  resource-faithful bridge — a proved comparison
  `CircuitSize ≥ R/p` with polynomial `p`, together with
  superpolynomial growth of the resource `R` on the family,
  excludes every polynomial circuit-size bound (the rendered
  `L ∉ P/poly` conclusion).

Rendering disclosed: the identification of `CircuitSize` with a
concrete Boolean-circuit complexity measure, the NP-completeness
of the target language, and the two missing inputs (the resource
comparison and the superpolynomial loading bound, per the
manuscript's complexity-scope firewall) are the displayed
hypotheses; nothing here claims either input.
-/

namespace NCG

/-- `prop:PvsNP-dimension-master`, dimension half: an orthonormal
family of `m` record vectors forces ambient dimension `≥ m`. -/
theorem record_dimension_firewall {m d : ℕ}
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hv : Orthonormal ℂ v) : m ≤ d := by
  have h := hv.linearIndependent.fintype_card_le_finrank
  simpa [Fintype.card_fin, finrank_euclideanSpace_fin] using h

/-- All `2ⁿ` Boolean inputs represented orthonormally force
ambient dimension at least `2ⁿ`. -/
theorem boolean_record_dimension {n d : ℕ}
    (v : Fin (2 ^ n) → EuclideanSpace ℂ (Fin d))
    (hv : Orthonormal ℂ v) : 2 ^ n ≤ d :=
  record_dimension_firewall v hv

/-- The xor chain shifts its seed to the front. -/
theorem foldl_xor_shift (t : List Bool) (b : Bool) :
    t.foldl xor b = xor b (t.foldl xor false) := by
  induction t generalizing b with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (xor b a),
      ih (xor false a)]
    cases a <;> cases b <;> simp

/-- Parity is computed by the linear chain of `xor` gates: the
fold over the input bits returns `true` exactly for an odd number
of `true` inputs. -/
theorem parity_fold_iff (l : List Bool) :
    l.foldl xor false = true ↔ Odd (l.count true) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, foldl_xor_shift]
    cases a
    · simpa using ih
    · have hcnt : List.count true (true :: t)
          = List.count true t + 1 := by simp
      rw [hcnt, Nat.odd_add_one, ← ih]
      cases t.foldl xor false <;> simp

/-- Superpolynomial growth of a resource functional. -/
def Superpoly (R : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    C * (n : ℝ) ^ k < R n

/-- `thm:PvsNP-bridge-master`: a proved comparison
`CircuitSize ≥ R/p` with polynomial `p` and superpolynomial
resource growth exclude every polynomial circuit-size bound. -/
theorem pvsnp_bridge (CS R p : ℕ → ℝ) (hp : ∀ n, 1 ≤ p n)
    (hpoly : ∃ (Cp : ℝ) (kp : ℕ), 0 < Cp
      ∧ ∀ n : ℕ, 1 ≤ n → p n ≤ Cp * (n : ℝ) ^ kp)
    (hcomp : ∀ n, R n / p n ≤ CS n)
    (hsuper : Superpoly R) :
    ¬ ∃ (C : ℝ) (k : ℕ), 0 < C
      ∧ ∀ n : ℕ, 1 ≤ n → CS n ≤ C * (n : ℝ) ^ k := by
  rintro ⟨C, k, hC, hbound⟩
  obtain ⟨Cp, kp, hCp, hpb⟩ := hpoly
  obtain ⟨N, hN⟩ := hsuper (C * Cp) (by positivity) (k + kp)
  set n := max N 1 with hn
  have hn1 : 1 ≤ n := le_max_right _ _
  have hnN : N ≤ n := le_max_left _ _
  have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hpn : (0 : ℝ) < p n := lt_of_lt_of_le one_pos (hp n)
  have h1 := hN n hnN
  have hRpos : (0 : ℝ) < R n :=
    lt_trans (by positivity) h1
  have hCS : (0 : ℝ) < CS n :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < R n / p n)
      (hcomp n)
  have h2 : R n ≤ CS n * p n := by
    have h := hcomp n
    calc R n = R n / p n * p n := by field_simp
      _ ≤ CS n * p n :=
        mul_le_mul_of_nonneg_right h hpn.le
  have h3 : CS n * p n ≤ C * (n : ℝ) ^ k * (Cp * (n : ℝ) ^ kp) :=
    mul_le_mul (hbound n hn1) (hpb n hn1) hpn.le
      (by positivity)
  have h4 : C * (n : ℝ) ^ k * (Cp * (n : ℝ) ^ kp)
      = C * Cp * (n : ℝ) ^ (k + kp) := by
    rw [pow_add]
    ring
  linarith [h1, h2, h3, h4.le, h4.ge]

end NCG
