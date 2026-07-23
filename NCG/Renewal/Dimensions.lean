/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.PredictiveQuotient

/-!
# The predictive dimensions `q_alg` and `q_met`

* **Definition `def:qalg`** (algebraic predictive dimension): the
  polynomial growth exponent of the number `N_CP(R)` of predictive
  classes with quotient length `≤ R`,
  `q_alg = limsup log N_CP(R) / log R`
  (`NCG.RenewalMemory.algebraicDimension`).  Its well-posedness is the
  **finite-shell theorem** (`NCG.RenewalMemory.shell_finite`, Remark
  `rem:compact-resolvent-finite-balls`): over a finite alphabet each
  length shell is finite, because every class of quotient length
  `≤ R` has a representative word of length `≤ R − 1` — this is also
  the compact-resolvent input of Theorem `thm:triple`.

* **Definition `def:qmet`** (metric predictive dimension): the upper
  box dimension of the accumulated-channel set, encoded abstractly for
  a pseudometric space via covering numbers
  (`NCG.coveringNumber`, `NCG.upperBoxDimension`).  The completely
  bounded norm geometry on channels is not yet formalised, so `q_met`
  is stated for an abstract metric model. -/

namespace NCG.RenewalMemory

open Filter

variable {E M : Type*} [Monoid M] (R : RenewalMemory E M)

/-- The **length shell**: predictive classes of quotient length `≤ n`
(Definition `def:qalg`, Remark `rem:compact-resolvent-finite-balls`). -/
def shell (n : ℕ) : Set R.PredictiveQuotient :=
  {x | R.quotLength x ≤ n}

/-- **Finite shells** (Remark `rem:compact-resolvent-finite-balls`, the
compact-resolvent input of Theorem `thm:triple`): over a finite alphabet
every length shell is finite — each class of quotient length `≤ n` has a
representative word of length `< n` over `E`. -/
theorem shell_finite [Finite E] (n : ℕ) : (R.shell n).Finite := by
  have hwords : {w : History E | w.length ≤ n}.Finite :=
    List.finite_length_le E n
  apply Set.Finite.subset (hwords.image R.mkQ)
  intro x hx
  obtain ⟨w, hw, hlen⟩ := R.exists_quotLength_rep x
  have hxn : R.quotLength x ≤ n := hx
  rw [hlen] at hxn
  have hwn : w.length ≤ n := by omega
  exact ⟨w, hwn, hw⟩

/-- `N_CP(n)`: the number of distinguishable accumulated channels of
quotient length `≤ n` (Definition `def:qalg`). -/
noncomputable def channelCount (n : ℕ) : ℕ := (R.shell n).ncard

/-- The empty class lies in every shell of radius `≥ 1`, so the channel
count is positive. -/
theorem channelCount_pos [Finite E] {n : ℕ} (hn : 1 ≤ n) :
    0 < R.channelCount n := by
  have hmem : R.mkQ 1 ∈ R.shell n := by
    show R.quotLength (R.mkQ 1) ≤ n
    rw [R.quotLength_one]
    exact hn
  exact Set.ncard_pos (R.shell_finite n) |>.mpr ⟨R.mkQ 1, hmem⟩

/-- The channel count is monotone in the shell radius. -/
theorem channelCount_mono [Finite E] {m n : ℕ} (h : m ≤ n) :
    R.channelCount m ≤ R.channelCount n :=
  Set.ncard_le_ncard (fun _ hx => le_trans hx h) (R.shell_finite n)

/-- **Definition `def:qalg`** (algebraic predictive dimension): the
polynomial growth exponent of distinguishable accumulated channels as a
function of quotient length. -/
noncomputable def algebraicDimension [Finite E] : ℝ :=
  limsup (fun n : ℕ => Real.log (R.channelCount n) / Real.log n) atTop

end NCG.RenewalMemory

namespace NCG

open Filter

variable {X : Type*} [PseudoMetricSpace X]

/-- The **covering number** `N(δ)`: the minimal size of a finite set of
`δ`-ball centres covering `s` (Definition `def:qmet`). -/
noncomputable def coveringNumber (s : Set X) (δ : ℝ) : ℕ :=
  sInf {n : ℕ | ∃ t : Finset X, t.card = n ∧
    s ⊆ ⋃ y ∈ t, Metric.ball y δ}

/-- **Definition `def:qmet`** (metric predictive dimension): the upper
box dimension `limsup log N(δ) / log(1/δ)` of the closure of the
accumulated-channel set — stated for an abstract pseudometric model of
the completely bounded channel geometry. -/
noncomputable def upperBoxDimension (s : Set X) : ℝ :=
  limsup (fun δ : ℝ => Real.log (coveringNumber s δ) / Real.log (1 / δ))
    (nhdsWithin 0 (Set.Ioi 0))

end NCG
