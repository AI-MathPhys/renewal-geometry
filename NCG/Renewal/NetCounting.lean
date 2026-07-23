/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.Dimensions

/-!
# Net and separation counting: metric–predictive coincidence

**Theorem `thm:metric-predictive-coincidence`** (counting core): under
two-sided channel coding — the degree-`R` channels `S_R` form a
`C/R`-net of the channel closure and are `c/R`-separated — the covering
numbers are sandwiched by the predictive count:

* a `δ`-net of size `N` bounds the covering number,
  `N_cb(δ) ≤ N` (`NCG.coveringNumber_le_of_net`);
* an `ε`-separated subset injects into any `ε/3`-cover,
  `#S ≤ N_cb(ε/3)` (`NCG.separated_card_le_of_cover`,
  `NCG.separated_le_coveringNumber`).

Taking logarithms along reciprocal scales gives `q_met = q_alg`; the
limsup bookkeeping is not formalised. -/

namespace NCG

variable {X : Type*} [PseudoMetricSpace X] {s : Set X}

/-- **Net bound** (`thm:metric-predictive-coincidence`, first
inequality): a finite `δ`-net of `s` bounds the covering number by its
cardinality. -/
theorem coveringNumber_le_of_net (t : Finset X) {δ : ℝ}
    (hcover : s ⊆ ⋃ y ∈ t, Metric.ball y δ) :
    coveringNumber s δ ≤ t.card :=
  Nat.sInf_le ⟨t, rfl, hcover⟩

/-- **Separation bound** (`thm:metric-predictive-coincidence`, second
inequality): an `ε`-separated subset of `s` injects into any
`ε/3`-ball cover — each ball contains at most one separated point. -/
theorem separated_card_le_of_cover (S : Finset X) (hS : ↑S ⊆ s)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ε ≤ dist a b)
    {t : Finset X} (hcover : s ⊆ ⋃ y ∈ t, Metric.ball y (ε / 3)) :
    S.card ≤ t.card := by
  have hassign : ∀ a : ↥S, ∃ y ∈ t, (a : X) ∈ Metric.ball y (ε / 3) := by
    intro a
    have := hcover (hS a.2)
    simpa [Set.mem_iUnion] using this
  choose f hf hball using hassign
  have hinj : Function.Injective
      (fun a : ↥S => (⟨f a, hf a⟩ : ↥t)) := by
    intro a b hab
    have heq : f a = f b := congrArg Subtype.val hab
    ext
    by_contra hne
    have h1 : dist (a : X) (f a) < ε / 3 := Metric.mem_ball.mp (hball a)
    have h2 : dist (b : X) (f b) < ε / 3 := Metric.mem_ball.mp (hball b)
    have hd : ε ≤ dist (a : X) (b : X) := hsep a a.2 b b.2 hne
    have htri : dist (a : X) (b : X)
        ≤ dist (a : X) (f a) + dist (f b) (b : X) := by
      calc dist (a : X) (b : X)
          ≤ dist (a : X) (f a) + dist (f a) (b : X) := dist_triangle _ _ _
        _ = dist (a : X) (f a) + dist (f b) (b : X) := by rw [heq]
    rw [dist_comm (f b) (b : X)] at htri
    linarith
  calc S.card = Fintype.card ↥S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card ↥t := Fintype.card_le_of_injective _ hinj
    _ = t.card := Fintype.card_coe t

/-- **Theorem `thm:metric-predictive-coincidence`** (sandwich): when a
finite `ε/3`-cover exists, an `ε`-separated subset of `s` is bounded by
the covering number: `#S ≤ N_cb(ε/3)` — with the net bound this
sandwiches the predictive count between covering numbers. -/
theorem separated_le_coveringNumber (S : Finset X) (hS : ↑S ⊆ s)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ε ≤ dist a b)
    (hcov : ∃ t : Finset X, s ⊆ ⋃ y ∈ t, Metric.ball y (ε / 3)) :
    S.card ≤ coveringNumber s (ε / 3) := by
  have hne : {n : ℕ | ∃ t : Finset X, t.card = n ∧
      s ⊆ ⋃ y ∈ t, Metric.ball y (ε / 3)}.Nonempty := by
    obtain ⟨t, ht⟩ := hcov
    exact ⟨t.card, t, rfl, ht⟩
  obtain ⟨t₀, ht₀card, ht₀cov⟩ := Nat.sInf_mem hne
  rw [coveringNumber, ← ht₀card]
  exact separated_card_le_of_cover S hS hε hsep ht₀cov

end NCG
