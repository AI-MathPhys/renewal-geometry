/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CanonicalFiniteRateFibreRefresh

/-!
# Coarse and hidden entropy production

Finite-state entropy production for a generator and its stationary reversal,
its exact split through a deterministic Markov retract, and the equality case
for the canonical stationary-decoder Poisson refresh lift.
-/

open Finset Matrix

namespace NCG
namespace CoarseAndHiddenEntropyProduction

/-- The scalar continuous-time rate divergence
`Phi(a,b) = a log(a/b) - a + b`. -/
noncomputable def rateDivergence (a b : ℝ) : ℝ :=
  a * Real.log (a / b) - a + b

theorem rateDivergence_self (a : ℝ) : rateDivergence a a = 0 := by
  simp [rateDivergence]

theorem rateDivergence_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ rateDivergence a b := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hrewrite : Real.log (a / b) = -Real.log (b / a) := by
    rw [Real.log_div ha.ne' hb.ne', Real.log_div hb.ne' ha.ne']
    ring
  rw [rateDivergence, hrewrite]
  have ha0 : 0 ≤ a := ha.le
  have hmul := mul_le_mul_of_nonneg_left hlog ha0
  have hratio : a * (b / a - 1) = b - a := by
    field_simp [ha.ne']
  rw [hratio] at hmul
  linarith

/-- Finite relative entropy of two strictly positive probability vectors. -/
noncomputable def finiteKL {I : Type*} [Fintype I]
    (p q : I → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

theorem finiteKL_nonneg {I : Type*} [Fintype I] [Nonempty I]
    (p q : I → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hpOne : ∑ i, p i = 1) (hqOne : ∑ i, q i = 1) :
    0 ≤ finiteKL p q := by
  have hpoint : ∀ i, p i * Real.log (q i / p i) ≤ q i - p i := by
    intro i
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (hq i) (hp i))) (hp i).le
    have heq : p i * (q i / p i - 1) = q i - p i := by
      field_simp [(hp i).ne']
    exact h.trans_eq heq
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset I)) => hpoint i
  have hlog (i : I) : Real.log (p i / q i) = -Real.log (q i / p i) := by
    rw [Real.log_div (hp i).ne' (hq i).ne',
      Real.log_div (hq i).ne' (hp i).ne']
    ring
  simp only [Finset.sum_sub_distrib, hpOne, hqOne, sub_self] at hsum
  unfold finiteKL
  simp_rw [hlog]
  calc
    0 ≤ -(∑ i, p i * Real.log (q i / p i)) := neg_nonneg.mpr hsum
    _ = ∑ i, p i * -Real.log (q i / p i) := by
      symm
      calc
        ∑ i, p i * -Real.log (q i / p i) =
            ∑ i, -(p i * Real.log (q i / p i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = -(∑ i, p i * Real.log (q i / p i)) :=
          by simpa using
            (Finset.sum_neg_distrib (s := (Finset.univ : Finset I))
              (f := fun i => p i * Real.log (q i / p i)))

/-- The log-sum identity, written as rate divergence plus normalized finite KL. -/
theorem sum_rateDivergence_eq_total_add_KL
    {I : Type*} [Fintype I] [Nonempty I]
    (a b : I → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    let A := ∑ i, a i
    let B := ∑ i, b i
    ∑ i, rateDivergence (a i) (b i) =
      rateDivergence A B + A * finiteKL (fun i => a i / A) (fun i => b i / B) := by
  dsimp
  have hA : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i)
    Finset.univ_nonempty
  have hB : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i)
    Finset.univ_nonempty
  unfold rateDivergence finiteKL
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hlog (i : I) :
      Real.log ((a i / (∑ j, a j)) / (b i / (∑ j, b j))) =
        Real.log (a i / b i) - Real.log ((∑ j, a j) / (∑ j, b j)) := by
    have hratio :
        (a i / (∑ j, a j)) / (b i / (∑ j, b j)) =
          (a i / b i) / ((∑ j, a j) / (∑ j, b j)) := by
      field_simp [(ha i).ne', (hb i).ne', hA.ne', hB.ne']
    rw [hratio, Real.log_div (div_ne_zero (ha i).ne' (hb i).ne')
        (div_ne_zero hA.ne' hB.ne'),
      Real.log_div (ha i).ne' (hb i).ne',
      Real.log_div hA.ne' hB.ne']
  simp_rw [hlog]
  have hscale :
      (∑ i, a i) *
          (∑ i, a i / (∑ j, a j) *
            (Real.log (a i / b i) - Real.log ((∑ j, a j) / (∑ j, b j)))) =
        ∑ i, a i *
          (Real.log (a i / b i) - Real.log ((∑ j, a j) / (∑ j, b j))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hA.ne']
  rw [hscale]
  have hsumExpand :
      (∑ i, a i *
        (Real.log (a i / b i) - Real.log ((∑ j, a j) / (∑ j, b j)))) =
        (∑ i, a i * Real.log (a i / b i)) -
          (∑ i, a i) * Real.log ((∑ j, a j) / (∑ j, b j)) := by
    calc
      (∑ i, a i *
          (Real.log (a i / b i) - Real.log ((∑ j, a j) / (∑ j, b j)))) =
          ∑ i, (a i * Real.log (a i / b i) -
            a i * Real.log ((∑ j, a j) / (∑ j, b j))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, a i * Real.log (a i / b i)) -
          ∑ i, a i * Real.log ((∑ j, a j) / (∑ j, b j)) :=
        by simpa using
          (Finset.sum_sub_distrib
            (s := (Finset.univ : Finset I))
            (f := fun i => a i * Real.log (a i / b i))
            (g := fun i => a i * Real.log ((∑ j, a j) / (∑ j, b j))))
      _ = (∑ i, a i * Real.log (a i / b i)) -
          (∑ i, a i) * Real.log ((∑ j, a j) / (∑ j, b j)) := by
        rw [Finset.sum_mul]
  rw [hsumExpand]
  ring

theorem sum_rateDivergence_ge_total
    {I : Type*} [Fintype I] [Nonempty I]
    (a b : I → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    rateDivergence (∑ i, a i) (∑ i, b i) ≤
      ∑ i, rateDivergence (a i) (b i) := by
  rw [sum_rateDivergence_eq_total_add_KL a b ha hb]
  apply le_add_of_nonneg_right
  apply mul_nonneg
  · exact (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty).le
  · apply finiteKL_nonneg
    · intro i
      exact div_pos (ha i) (Finset.sum_pos (fun j _ => ha j) Finset.univ_nonempty)
    · intro i
      exact div_pos (hb i) (Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty)
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt (Finset.sum_pos (fun i _ => ha i)
        Finset.univ_nonempty))
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt (Finset.sum_pos (fun i _ => hb i)
        Finset.univ_nonempty))

/-- The finite fibre of a deterministic state record. -/
abbrev Fibre {U Z : Type*} (c : U → Z) (z : Z) := {u : U // c u = z}

/-- A matrix is strongly lumpable in rate-sum form. -/
def BlockLumpable
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (L : Matrix U U ℝ) (A : Matrix Z Z ℝ) : Prop :=
  ∀ u z, ∑ v : Fibre c z, L u v.1 = A (c u) z

/-- A generator retract is lumpable both forward and after stationary
reversal.  This is the finite generator version of two-sided Markov
retractability. -/
structure GeneratorMarkovRetract
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ)
    (L : Matrix U U ℝ) (A : Matrix Z Z ℝ) : Prop where
  forward : BlockLumpable c L A
  reversed : BlockLumpable c
    (UniversalMarkovRetract.stationaryReversal m L)
    (UniversalMarkovRetract.coarseReversal c m A)

/-- Sum a finite family by the fibres of a deterministic record. -/
theorem sum_over_fibres
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (f : U → ℝ) :
    ∑ u, f u = ∑ z, ∑ u : Fibre c z, f u.1 := by
  classical
  symm
  calc
    (∑ z, ∑ u : Fibre c z, f u.1) =
        ∑ z, ∑ u ∈ (Finset.univ.filter fun u ↦ c u = z), f u := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_subtype
        (p := fun u ↦ c u = z)
        (Finset.univ.filter fun u ↦ c u = z) (by simp) f]
    _ = ∑ u, ∑ z, if c u = z then f u else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_filter]
    _ = ∑ u, f u := by simp

/-- Rate divergence contributed by destinations in one coarse fibre. -/
noncomputable def blockRateDivergence
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (L : Matrix U U ℝ)
    (u : U) (z : Z) : ℝ :=
  ∑ v : Fibre c z,
    rateDivergence (L u v.1)
      (UniversalMarkovRetract.stationaryReversal m L u v.1)

/-- Stationary entropy-production rate of a finite generator.  Diagonal
terms are harmless because stationary reversal fixes the diagonal. -/
noncomputable def stationaryEntropyProduction
    {U : Type*} [Fintype U]
    (m : U → ℝ) (L : Matrix U U ℝ) : ℝ :=
  ∑ u, m u * ∑ v,
    rateDivergence (L u v)
      (UniversalMarkovRetract.stationaryReversal m L u v)

/-- Entropy production of the coarse generator with its pushed-forward
stationary mass. -/
noncomputable def coarseEntropyProduction
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (A : Matrix Z Z ℝ) : ℝ :=
  ∑ z, UniversalMarkovRetract.cellMass c m z * ∑ z',
    rateDivergence (A z z')
      (UniversalMarkovRetract.coarseReversal c m A z z')

/-- Hidden entropy from irreversible choices of the fine destination within
a visible target fibre. -/
noncomputable def destinationHiddenEntropy
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ)
    (L : Matrix U U ℝ) (A : Matrix Z Z ℝ) : ℝ :=
  ∑ u, m u * ∑ z ∈ (Finset.univ.erase (c u)),
    (blockRateDivergence c m L u z -
      rateDivergence (A (c u) z)
        (UniversalMarkovRetract.coarseReversal c m A (c u) z))

/-- Hidden entropy from fine motion inside a record fibre. -/
noncomputable def internalHiddenEntropy
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (L : Matrix U U ℝ) : ℝ :=
  ∑ u, m u * blockRateDivergence c m L u (c u)

theorem cellMass_eq_sum_fibre
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (z : Z) :
    UniversalMarkovRetract.cellMass c m z = ∑ u : Fibre c z, m u.1 := by
  classical
  unfold UniversalMarkovRetract.cellMass
  rw [← Finset.sum_subtype
    (p := fun u ↦ c u = z)
    (Finset.univ.filter fun u ↦ c u = z) (by simp) m]
  rw [Finset.sum_filter]

theorem weighted_pullback_sum
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (g : Z → ℝ) :
    ∑ u, m u * g (c u) =
      ∑ z, UniversalMarkovRetract.cellMass c m z * g z := by
  rw [sum_over_fibres c (fun u => m u * g (c u))]
  apply Finset.sum_congr rfl
  intro z _
  rw [cellMass_eq_sum_fibre, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [u.property]

theorem stationaryReversal_diagonal
    {U : Type*} (m : U → ℝ) (L : Matrix U U ℝ) (u : U)
    (hm : 0 < m u) :
    UniversalMarkovRetract.stationaryReversal m L u u = L u u := by
  unfold UniversalMarkovRetract.stationaryReversal
  field_simp [hm.ne']

theorem coarseReversal_diagonal
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) (z : Z) :
    UniversalMarkovRetract.coarseReversal c m A z z = A z z := by
  have hmass := UniversalMarkovRetract.cellMass_pos c hc m hm z
  unfold UniversalMarkovRetract.coarseReversal
  field_simp [hmass.ne']

theorem stationaryEntropyProduction_eq_blocks
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (L : Matrix U U ℝ) :
    stationaryEntropyProduction m L =
      ∑ u, m u * ∑ z, blockRateDivergence c m L u z := by
  unfold stationaryEntropyProduction blockRateDivergence
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  exact sum_over_fibres c (fun v =>
    rateDivergence (L u v)
      (UniversalMarkovRetract.stationaryReversal m L u v))

theorem coarseEntropyProduction_eq_lifted
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) :
    coarseEntropyProduction c m A =
      ∑ u, m u * ∑ z ∈ (Finset.univ.erase (c u)),
        rateDivergence (A (c u) z)
          (UniversalMarkovRetract.coarseReversal c m A (c u) z) := by
  let g : Z → ℝ := fun z =>
    ∑ z' ∈ (Finset.univ.erase z),
      rateDivergence (A z z')
        (UniversalMarkovRetract.coarseReversal c m A z z')
  calc
    coarseEntropyProduction c m A =
        ∑ z, UniversalMarkovRetract.cellMass c m z * g z := by
      unfold coarseEntropyProduction g
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z)]
      rw [coarseReversal_diagonal c hc m hm A z,
        rateDivergence_self, add_zero]
    _ = ∑ u, m u * g (c u) := (weighted_pullback_sum c m g).symm
    _ = _ := rfl

/-- The boxed finite-state entropy split.  The content is not an algebraic
placeholder: `stationaryEntropyProduction` is the directed CT rate divergence,
and the coarse term is the corresponding divergence for the pushed-forward
stationary law. -/
theorem coarse_and_hidden_entropy_production
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (L : Matrix U U ℝ) (A : Matrix Z Z ℝ) :
    stationaryEntropyProduction m L =
      coarseEntropyProduction c m A +
        destinationHiddenEntropy c m L A +
        internalHiddenEntropy c m L := by
  rw [stationaryEntropyProduction_eq_blocks c m L,
    coarseEntropyProduction_eq_lifted c hc m hm A]
  unfold destinationHiddenEntropy internalHiddenEntropy
  calc
    (∑ u, m u * ∑ z, blockRateDivergence c m L u z) =
        ∑ u, (m u * ∑ z ∈ (Finset.univ.erase (c u)),
            rateDivergence (A (c u) z)
              (UniversalMarkovRetract.coarseReversal c m A (c u) z) +
          m u * ∑ z ∈ (Finset.univ.erase (c u)),
            (blockRateDivergence c m L u z -
              rateDivergence (A (c u) z)
                (UniversalMarkovRetract.coarseReversal c m A (c u) z)) +
          m u * blockRateDivergence c m L u (c u)) := by
      apply Finset.sum_congr rfl
      intro u _
      have hsplit :
          ∑ z, blockRateDivergence c m L u z =
            (∑ z ∈ (Finset.univ.erase (c u)),
              blockRateDivergence c m L u z) +
              blockRateDivergence c m L u (c u) := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ (c u))]
      have hdiff :
          (∑ z ∈ (Finset.univ.erase (c u)),
            (blockRateDivergence c m L u z -
              rateDivergence (A (c u) z)
                (UniversalMarkovRetract.coarseReversal c m A (c u) z))) =
          (∑ z ∈ (Finset.univ.erase (c u)),
            blockRateDivergence c m L u z) -
          ∑ z ∈ (Finset.univ.erase (c u)),
            rateDivergence (A (c u) z)
              (UniversalMarkovRetract.coarseReversal c m A (c u) z) := by
        simpa using
          (Finset.sum_sub_distrib
            (s := (Finset.univ.erase (c u)))
            (f := fun z => blockRateDivergence c m L u z)
            (g := fun z => rateDivergence (A (c u) z)
              (UniversalMarkovRetract.coarseReversal c m A (c u) z)))
      rw [hsplit, hdiff]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem internal_block_entropy_nonneg
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (L : Matrix U U ℝ)
    (hRates : ∀ u v, u ≠ v → 0 < L u v)
    (u : U) :
    0 ≤ blockRateDivergence c m L u (c u) := by
  unfold blockRateDivergence
  apply Finset.sum_nonneg
  intro v _
  by_cases hvu : v.1 = u
  · rw [hvu, stationaryReversal_diagonal m L u (hm u),
      rateDivergence_self]
  · apply rateDivergence_nonneg (hRates u v.1 (Ne.symm hvu))
    unfold UniversalMarkovRetract.stationaryReversal
    exact div_pos (mul_pos (hm v.1) (hRates v.1 u hvu)) (hm u)

theorem visible_block_entropy_excess_nonneg
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (L : Matrix U U ℝ) (A : Matrix Z Z ℝ)
    (R : GeneratorMarkovRetract c m L A)
    (hRates : ∀ u v, u ≠ v → 0 < L u v)
    (u : U) (z : Z) (huz : z ≠ c u) :
    0 ≤ blockRateDivergence c m L u z -
      rateDivergence (A (c u) z)
        (UniversalMarkovRetract.coarseReversal c m A (c u) z) := by
  obtain ⟨v0, hv0⟩ := hc z
  letI : Nonempty (Fibre c z) := ⟨⟨v0, hv0⟩⟩
  have hne (v : Fibre c z) : u ≠ v.1 := by
    intro huv
    apply huz
    rw [huv, v.property]
  have hforward (v : Fibre c z) : 0 < L u v.1 :=
    hRates u v.1 (hne v)
  have hreverse (v : Fibre c z) :
      0 < UniversalMarkovRetract.stationaryReversal m L u v.1 := by
    unfold UniversalMarkovRetract.stationaryReversal
    exact div_pos
      (mul_pos (hm v.1) (hRates v.1 u (Ne.symm (hne v)))) (hm u)
  have hsum := sum_rateDivergence_ge_total
    (fun v : Fibre c z => L u v.1)
    (fun v : Fibre c z =>
      UniversalMarkovRetract.stationaryReversal m L u v.1)
    hforward hreverse
  rw [R.forward u z, R.reversed u z] at hsum
  unfold blockRateDivergence
  linarith

theorem destinationHiddenEntropy_nonneg
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (L : Matrix U U ℝ) (A : Matrix Z Z ℝ)
    (R : GeneratorMarkovRetract c m L A)
    (hRates : ∀ u v, u ≠ v → 0 < L u v) :
    0 ≤ destinationHiddenEntropy c m L A := by
  unfold destinationHiddenEntropy
  apply Finset.sum_nonneg
  intro u _
  apply mul_nonneg (hm u).le
  apply Finset.sum_nonneg
  intro z hz
  have huz : z ≠ c u := by
    exact (Finset.mem_erase.mp hz).1
  exact visible_block_entropy_excess_nonneg c hc m hm L A R hRates u z huz

theorem internalHiddenEntropy_nonneg
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (L : Matrix U U ℝ)
    (hRates : ∀ u v, u ≠ v → 0 < L u v) :
    0 ≤ internalHiddenEntropy c m L := by
  unfold internalHiddenEntropy
  apply Finset.sum_nonneg
  intro u _
  exact mul_nonneg (hm u).le
    (internal_block_entropy_nonneg c m hm L hRates u)

/-- Both hidden coordinates of a finite generator Markov retract are
nonnegative.  Strict bidirected off-diagonal rates avoid extended-real
conventions at zero; the decomposition theorem itself needs no such
restriction. -/
theorem hidden_entropy_coordinates_nonnegative
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (L : Matrix U U ℝ) (A : Matrix Z Z ℝ)
    (R : GeneratorMarkovRetract c m L A)
    (hRates : ∀ u v, u ≠ v → 0 < L u v) :
    0 ≤ destinationHiddenEntropy c m L A ∧
      0 ≤ internalHiddenEntropy c m L :=
  ⟨destinationHiddenEntropy_nonneg c hc m hm L A R hRates,
    internalHiddenEntropy_nonneg c m hm L hRates⟩

theorem embedded_coarse_generator_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (A : Matrix Z Z ℝ) (u v : U) :
    (UniversalMarkovRetract.recordMatrix c * A *
      UniversalMarkovRetract.stationaryDecoder c m) u v =
      A (c u) (c v) * m v /
        UniversalMarkovRetract.cellMass c m (c v) := by
  classical
  simp [Matrix.mul_apply, UniversalMarkovRetract.recordMatrix,
    UniversalMarkovRetract.stationaryDecoder]
  ring

theorem conditional_expectation_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (u v : U) :
    (UniversalMarkovRetract.recordMatrix c *
      UniversalMarkovRetract.stationaryDecoder c m) u v =
      if c u = c v then
        m v / UniversalMarkovRetract.cellMass c m (c v)
      else 0 := by
  classical
  simp [Matrix.mul_apply, UniversalMarkovRetract.recordMatrix,
    UniversalMarkovRetract.stationaryDecoder]

/-- The canonical Poisson refresh generator specialized to a deterministic
record and its stationary conditional decoder. -/
noncomputable def stationaryRefreshGenerator
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (A : Matrix Z Z ℝ) (lam : ℝ) :
    Matrix U U ℝ :=
  CanonicalFiniteRateFibreRefresh.refreshGenerator
    (UniversalMarkovRetract.recordMatrix c)
    (UniversalMarkovRetract.stationaryDecoder c m) A lam

theorem stationaryRefreshGenerator_offdiagonal_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (A : Matrix Z Z ℝ) (lam : ℝ)
    (u v : U) (huv : u ≠ v) :
    stationaryRefreshGenerator c m A lam u v =
      A (c u) (c v) * m v /
          UniversalMarkovRetract.cellMass c m (c v) +
        lam * (if c u = c v then
          m v / UniversalMarkovRetract.cellMass c m (c v) else 0) := by
  unfold stationaryRefreshGenerator
  simp only [CanonicalFiniteRateFibreRefresh.refreshGenerator,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [embedded_coarse_generator_apply,
    conditional_expectation_apply]
  simp [Matrix.one_apply, huv]

theorem stationaryRefreshGenerator_visible_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (A : Matrix Z Z ℝ) (lam : ℝ)
    (u v : U) (hcell : c u ≠ c v) :
    stationaryRefreshGenerator c m A lam u v =
      A (c u) (c v) *
        (m v / UniversalMarkovRetract.cellMass c m (c v)) := by
  have huv : u ≠ v := fun h => hcell (congrArg c h)
  rw [stationaryRefreshGenerator_offdiagonal_apply c m A lam u v huv]
  simp [hcell]
  ring

theorem stationaryRefreshGenerator_internal_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (A : Matrix Z Z ℝ) (lam : ℝ)
    (u v : U) (huv : u ≠ v) (hcell : c u = c v) :
    stationaryRefreshGenerator c m A lam u v =
      (A (c u) (c u) + lam) *
        (m v / UniversalMarkovRetract.cellMass c m (c u)) := by
  rw [stationaryRefreshGenerator_offdiagonal_apply c m A lam u v huv]
  simp [hcell]
  ring

theorem stationaryRefreshReversal_visible_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) (lam : ℝ)
    (u v : U) (hcell : c u ≠ c v) :
    UniversalMarkovRetract.stationaryReversal m
        (stationaryRefreshGenerator c m A lam) u v =
      UniversalMarkovRetract.coarseReversal c m A (c u) (c v) *
        (m v / UniversalMarkovRetract.cellMass c m (c v)) := by
  have hmassU := UniversalMarkovRetract.cellMass_pos c hc m hm (c u)
  have hmassV := UniversalMarkovRetract.cellMass_pos c hc m hm (c v)
  unfold UniversalMarkovRetract.stationaryReversal
  rw [stationaryRefreshGenerator_visible_apply c m A lam v u (Ne.symm hcell)]
  unfold UniversalMarkovRetract.coarseReversal
  field_simp [hmassU.ne', hmassV.ne', (hm u).ne', (hm v).ne']

theorem stationaryRefreshReversal_internal_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) (lam : ℝ)
    (u v : U) (huv : u ≠ v) (hcell : c u = c v) :
    UniversalMarkovRetract.stationaryReversal m
        (stationaryRefreshGenerator c m A lam) u v =
      stationaryRefreshGenerator c m A lam u v := by
  have hmass := UniversalMarkovRetract.cellMass_pos c hc m hm (c u)
  unfold UniversalMarkovRetract.stationaryReversal
  rw [stationaryRefreshGenerator_internal_apply c m A lam v u
      (Ne.symm huv) hcell.symm,
    stationaryRefreshGenerator_internal_apply c m A lam u v huv hcell]
  rw [hcell]
  field_simp [hmass.ne', (hm u).ne', (hm v).ne']

theorem rateDivergence_common_weight
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    rateDivergence (a * r) (b * r) = r * rateDivergence a b := by
  have hratio : (a * r) / (b * r) = a / b := by
    field_simp [ha.ne', hb.ne', hr.ne']
  unfold rateDivergence
  rw [hratio]
  ring

theorem stationaryDecoder_weights_sum
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u) (z : Z) :
    ∑ v : Fibre c z,
      m v.1 / UniversalMarkovRetract.cellMass c m z = 1 := by
  rw [← Finset.sum_div, ← cellMass_eq_sum_fibre]
  exact div_self
    (UniversalMarkovRetract.cellMass_pos c hc m hm z).ne'

theorem stationaryRefresh_visible_block_has_no_hidden_entropy
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) (lam : ℝ)
    (u : U) (z : Z) (huz : z ≠ c u)
    (hforward : 0 < A (c u) z) (hback : 0 < A z (c u)) :
    blockRateDivergence c m (stationaryRefreshGenerator c m A lam) u z =
      rateDivergence (A (c u) z)
        (UniversalMarkovRetract.coarseReversal c m A (c u) z) := by
  have hmassU := UniversalMarkovRetract.cellMass_pos c hc m hm (c u)
  have hmassZ := UniversalMarkovRetract.cellMass_pos c hc m hm z
  have hbackward :
      0 < UniversalMarkovRetract.coarseReversal c m A (c u) z := by
    unfold UniversalMarkovRetract.coarseReversal
    exact div_pos (mul_pos hmassZ hback) hmassU
  unfold blockRateDivergence
  calc
    (∑ v : Fibre c z,
        rateDivergence
          (stationaryRefreshGenerator c m A lam u v.1)
          (UniversalMarkovRetract.stationaryReversal m
            (stationaryRefreshGenerator c m A lam) u v.1)) =
        ∑ v : Fibre c z,
          (m v.1 / UniversalMarkovRetract.cellMass c m z) *
            rateDivergence (A (c u) z)
              (UniversalMarkovRetract.coarseReversal c m A (c u) z) := by
      apply Finset.sum_congr rfl
      intro v _
      have hcell : c u ≠ c v.1 := by
        rw [v.property]
        exact Ne.symm huz
      rw [stationaryRefreshGenerator_visible_apply c m A lam u v.1 hcell,
        stationaryRefreshReversal_visible_apply c hc m hm A lam u v.1 hcell,
        v.property]
      exact rateDivergence_common_weight hforward hbackward
        (div_pos (hm v.1) hmassZ)
    _ = (∑ v : Fibre c z,
          m v.1 / UniversalMarkovRetract.cellMass c m z) *
            rateDivergence (A (c u) z)
              (UniversalMarkovRetract.coarseReversal c m A (c u) z) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [stationaryDecoder_weights_sum c hc m hm z, one_mul]

theorem stationaryRefresh_visible_zero_block
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) (lam : ℝ)
    (u : U) (z : Z) (huz : z ≠ c u)
    (hforward : A (c u) z = 0) (hback : A z (c u) = 0) :
    blockRateDivergence c m (stationaryRefreshGenerator c m A lam) u z = 0 ∧
      rateDivergence (A (c u) z)
        (UniversalMarkovRetract.coarseReversal c m A (c u) z) = 0 := by
  have hmassU := UniversalMarkovRetract.cellMass_pos c hc m hm (c u)
  have hcoarseRev :
      UniversalMarkovRetract.coarseReversal c m A (c u) z = 0 := by
    unfold UniversalMarkovRetract.coarseReversal
    rw [hback]
    simp
  constructor
  · unfold blockRateDivergence
    apply Finset.sum_eq_zero
    intro v _
    have hcell : c u ≠ c v.1 := by
      rw [v.property]
      exact Ne.symm huz
    rw [stationaryRefreshGenerator_visible_apply c m A lam u v.1 hcell,
      stationaryRefreshReversal_visible_apply c hc m hm A lam u v.1 hcell,
      v.property, hforward, hcoarseRev]
    simp [rateDivergence]
  · rw [hforward, hcoarseRev]
    simp [rateDivergence]

theorem stationaryRefresh_internal_block_has_no_hidden_entropy
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) (lam : ℝ) (u : U) :
    blockRateDivergence c m (stationaryRefreshGenerator c m A lam) u (c u) = 0 := by
  unfold blockRateDivergence
  apply Finset.sum_eq_zero
  intro v _
  by_cases hvu : v.1 = u
  · rw [hvu, stationaryReversal_diagonal m
      (stationaryRefreshGenerator c m A lam) u (hm u),
      rateDivergence_self]
  · have huv : u ≠ v.1 := Ne.symm hvu
    have hcell : c u = c v.1 := v.property.symm
    rw [stationaryRefreshReversal_internal_apply c hc m hm A lam
      u v.1 huv hcell, rateDivergence_self]

theorem stationaryRefresh_hidden_entropies_vanish
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) (lam : ℝ)
    (hSupport : ∀ x z, x ≠ z →
      (A x z = 0 ∧ A z x = 0) ∨ (0 < A x z ∧ 0 < A z x)) :
    destinationHiddenEntropy c m (stationaryRefreshGenerator c m A lam) A = 0 ∧
      internalHiddenEntropy c m (stationaryRefreshGenerator c m A lam) = 0 := by
  constructor
  · unfold destinationHiddenEntropy
    apply Finset.sum_eq_zero
    intro u _
    have hinner :
        (∑ z ∈ (Finset.univ.erase (c u)),
          (blockRateDivergence c m (stationaryRefreshGenerator c m A lam) u z -
            rateDivergence (A (c u) z)
              (UniversalMarkovRetract.coarseReversal c m A (c u) z))) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have huz : z ≠ c u := (Finset.mem_erase.mp hz).1
      rcases hSupport (c u) z (Ne.symm huz) with hzero | hpos
      · have hboth := stationaryRefresh_visible_zero_block
          c hc m hm A lam u z huz hzero.1 hzero.2
        rw [hboth.1, hboth.2, sub_self]
      · rw [stationaryRefresh_visible_block_has_no_hidden_entropy
          c hc m hm A lam u z huz hpos.1 hpos.2, sub_self]
    rw [hinner, mul_zero]
  · unfold internalHiddenEntropy
    apply Finset.sum_eq_zero
    intro u _
    rw [stationaryRefresh_internal_block_has_no_hidden_entropy
      c hc m hm A lam u, mul_zero]

/-- The refresh edges are reversible and the stationary-decoder lift uses the
same fine destination law in both time directions.  Consequently both hidden
terms vanish and the Poisson refresh lift preserves entropy production
exactly. -/
theorem stationaryRefresh_preserves_entropy_production
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c)
    (m : U → ℝ) (hm : ∀ u, 0 < m u)
    (A : Matrix Z Z ℝ) (lam : ℝ)
    (hSupport : ∀ x z, x ≠ z →
      (A x z = 0 ∧ A z x = 0) ∨ (0 < A x z ∧ 0 < A z x)) :
    stationaryEntropyProduction m (stationaryRefreshGenerator c m A lam) =
      coarseEntropyProduction c m A := by
  have hzero := stationaryRefresh_hidden_entropies_vanish
    c hc m hm A lam hSupport
  rw [coarse_and_hidden_entropy_production c hc m hm
      (stationaryRefreshGenerator c m A lam) A,
    hzero.1, hzero.2, add_zero, add_zero]

end CoarseAndHiddenEntropyProduction
end NCG
