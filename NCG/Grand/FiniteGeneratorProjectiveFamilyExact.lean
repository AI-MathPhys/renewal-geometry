/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteOrderedMarkovMarginalExact
import NCG.Grand.FiniteStateProjectiveLimitExact

/-!
# Finite-set laws for a continuous-time finite-state generator

This file transports the chronologically ordered tuple laws of a finite
generator to laws indexed by arbitrary finite subsets of nonnegative time.
The order is canonical, supplied by `Finset.orderIsoOfFin`; the state tuple
is then reindexed by the induced equivalence of dependent function spaces.
-/

open Matrix Finset
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace NCG.FiniteGeneratorProjectiveFamily

open NCG.FiniteOrderedMarkovMarginal

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Increasing enumeration, as real times, of a finite subset of
nonnegative real time. -/
def orderedTimes (J : Finset ℝ≥0) : Fin J.card → ℝ :=
  fun i => ((J.orderIsoOfFin rfl i : J) : ℝ≥0)

/-- The same increasing enumeration with its cardinality exposed as an
explicit equality.  This form is convenient when one point is inserted or
deleted and the tuple length must be visibly a successor. -/
def orderedTimesWithCard (J : Finset ℝ≥0) {n : ℕ}
    (hcard : J.card = n) : Fin n → ℝ :=
  fun i => ((J.orderIsoOfFin hcard i : J) : ℝ≥0)

theorem orderedTimesWithCard_rfl (J : Finset ℝ≥0) :
    orderedTimesWithCard J rfl = orderedTimes J := rfl

theorem orderedTimesWithCard_monotone (J : Finset ℝ≥0) {n : ℕ}
    (hcard : J.card = n) : Monotone (orderedTimesWithCard J hcard) := by
  intro i j hij
  exact_mod_cast (J.orderIsoOfFin hcard).monotone hij

theorem orderedTimesWithCard_nonnegative (J : Finset ℝ≥0) {n : ℕ}
    (hcard : J.card = n) (i : Fin n) :
    0 ≤ orderedTimesWithCard J hcard i := by
  exact NNReal.zero_le_coe

theorem orderedTimes_monotone (J : Finset ℝ≥0) :
    Monotone (orderedTimes J) := by
  intro i j hij
  exact_mod_cast (J.orderIsoOfFin rfl).monotone hij

theorem orderedTimes_nonnegative (J : Finset ℝ≥0)
    (i : Fin J.card) :
    0 ≤ orderedTimes J i := by
  exact NNReal.zero_le_coe

/-- Reindex a state tuple along the canonical increasing enumeration of a
finite time set. -/
def orderedStateEquiv (J : Finset ℝ≥0) :
    (Fin J.card → S) ≃ (J → S) :=
  Equiv.piCongrLeft (fun _ : J => S) (J.orderIsoOfFin rfl).toEquiv

/-- State-tuple reindexing with an explicitly supplied cardinality. -/
def orderedStateEquivWithCard (J : Finset ℝ≥0) {n : ℕ}
    (hcard : J.card = n) : (Fin n → S) ≃ (J → S) :=
  Equiv.piCongrLeft (fun _ : J => S) (J.orderIsoOfFin hcard).toEquiv

theorem orderedStateEquivWithCard_rfl (J : Finset ℝ≥0) :
    orderedStateEquivWithCard (S := S) J rfl = orderedStateEquiv J := rfl

/-- Deleting a point from a canonically ordered finite time set deletes
exactly the corresponding coordinate from its increasing enumeration. -/
theorem removeNth_orderedTimesWithCard_insert
    (J : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∉ J) :
    let I := insert t J
    let hcard : I.card = J.card + 1 := by simp [I, ht]
    let q : Fin (J.card + 1) :=
      (I.orderIsoOfFin hcard).symm ⟨t, by simp [I]⟩
    q.removeNth (orderedTimesWithCard I hcard) = orderedTimes J := by
  dsimp only
  let I : Finset ℝ≥0 := insert t J
  have hcard : I.card = J.card + 1 := by simp [I, ht]
  let q : Fin (J.card + 1) :=
    (I.orderIsoOfFin hcard).symm ⟨t, by simp [I]⟩
  change q.removeNth (orderedTimesWithCard I hcard) = orderedTimes J
  have hmem (i : Fin J.card) :
      ((I.orderIsoOfFin hcard (q.succAbove i) : I) : ℝ≥0) ∈ J := by
    have hne :
        ((I.orderIsoOfFin hcard (q.succAbove i) : I) : ℝ≥0) ≠ t := by
      intro heq
      have hsub : I.orderIsoOfFin hcard (q.succAbove i) =
          I.orderIsoOfFin hcard q := by
        apply Subtype.ext
        simpa [q] using heq
      exact Fin.succAbove_ne q i ((I.orderIsoOfFin hcard).injective hsub)
    exact (Finset.mem_insert.mp
      (I.orderIsoOfFin hcard (q.succAbove i)).property).resolve_left hne
  have henum :
      (fun i : Fin J.card =>
        ((I.orderIsoOfFin hcard (q.succAbove i) : I) : ℝ≥0)) =
        J.orderEmbOfFin rfl := by
    apply Finset.orderEmbOfFin_unique rfl hmem
    exact (I.orderIsoOfFin hcard).strictMono.comp
      (Fin.strictMono_succAbove q)
  funext i
  change (((I.orderIsoOfFin hcard (q.succAbove i) : I) : ℝ≥0) : ℝ) =
    orderedTimes J i
  exact congrArg (fun x : ℝ≥0 => (x : ℝ)) (congr_fun henum i)

/-- Restriction of assignments along `J ⊆ insert t J` commutes with the
canonical chronological tuple equivalences and deletion of the coordinate
occupied by `t`. -/
theorem restrict_orderedStateEquivWithCard_insert
    (J : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∉ J)
    (states : Fin (J.card + 1) → S) :
    let I := insert t J
    let hcard : I.card = J.card + 1 := by simp [I, ht]
    let q : Fin (J.card + 1) :=
      (I.orderIsoOfFin hcard).symm ⟨t, by simp [I]⟩
    Finset.restrict₂ (π := fun _ : ℝ≥0 => S)
        (show J ⊆ I by simp [I])
        (orderedStateEquivWithCard I hcard states) =
      orderedStateEquiv J (q.removeNth states) := by
  dsimp only
  let I : Finset ℝ≥0 := insert t J
  have hcard : I.card = J.card + 1 := by simp [I, ht]
  let q : Fin (J.card + 1) :=
    (I.orderIsoOfFin hcard).symm ⟨t, by simp [I]⟩
  have hJI : J ⊆ I := by simp [I]
  change Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI
      (orderedStateEquivWithCard I hcard states) =
    orderedStateEquiv J (q.removeNth states)
  funext j
  simp only [Finset.restrict₂, orderedStateEquivWithCard,
    orderedStateEquiv, Equiv.piCongrLeft_apply, Fin.removeNth,
    eq_rec_constant]
  congr 1
  apply (I.orderIsoOfFin hcard).injective
  apply Subtype.ext
  have hmem (i : Fin J.card) :
      ((I.orderIsoOfFin hcard (q.succAbove i) : I) : ℝ≥0) ∈ J := by
    have hne :
        ((I.orderIsoOfFin hcard (q.succAbove i) : I) : ℝ≥0) ≠ t := by
      intro heq
      have hsub : I.orderIsoOfFin hcard (q.succAbove i) =
          I.orderIsoOfFin hcard q := by
        apply Subtype.ext
        simpa [q] using heq
      exact Fin.succAbove_ne q i ((I.orderIsoOfFin hcard).injective hsub)
    exact (Finset.mem_insert.mp
      (I.orderIsoOfFin hcard (q.succAbove i)).property).resolve_left hne
  have henum :
      (fun i : Fin J.card =>
        ((I.orderIsoOfFin hcard (q.succAbove i) : I) : ℝ≥0)) =
        J.orderEmbOfFin rfl := by
    apply Finset.orderEmbOfFin_unique rfl hmem
    exact (I.orderIsoOfFin hcard).strictMono.comp
      (Fin.strictMono_succAbove q)
  calc
    ↑((I.orderIsoOfFin hcard)
        ((I.orderIsoOfFin hcard).symm ⟨j, hJI j.property⟩)) =
        (j : ℝ≥0) := congrArg Subtype.val
          ((I.orderIsoOfFin hcard).apply_symm_apply
            ⟨j, hJI j.property⟩)
    _ = J.orderEmbOfFin rfl ((J.orderIsoOfFin rfl).symm j) := by
      exact congrArg Subtype.val
        ((J.orderIsoOfFin rfl).apply_symm_apply j).symm
    _ = ↑((I.orderIsoOfFin hcard)
        (q.succAbove ((J.orderIsoOfFin rfl).symm j))) :=
      (congr_fun henum ((J.orderIsoOfFin rfl).symm j)).symm

/-- The generator law indexed by an arbitrary finite set of nonnegative
times. -/
def finiteTimeLaw
    (p : S → ℝ) (L : Matrix S S ℝ) (J : Finset ℝ≥0) :
    MeasureTheory.Measure (J → S) :=
  MeasureTheory.Measure.map (orderedStateEquiv J)
    (evolvedGeneratorFinChainLaw p L (orderedTimes J))

/-- The finite-set law written using an explicit proof of its cardinality. -/
def finiteTimeLawWithCard
    (p : S → ℝ) (L : Matrix S S ℝ) (J : Finset ℝ≥0)
    {n : ℕ} (hcard : J.card = n) :
    MeasureTheory.Measure (J → S) :=
  MeasureTheory.Measure.map (orderedStateEquivWithCard J hcard)
    (evolvedGeneratorFinChainLaw p L
      (orderedTimesWithCard J hcard))

theorem finiteTimeLawWithCard_eq
    (p : S → ℝ) (L : Matrix S S ℝ) (J : Finset ℝ≥0)
    {n : ℕ} (hcard : J.card = n) :
    finiteTimeLawWithCard p L J hcard = finiteTimeLaw p L J := by
  subst n
  rfl

/-- The mass of a finite-set atom is the chronologically ordered Markov
chain weight of that assignment. -/
theorem finiteTimeLaw_apply_singleton
    (p : S → ℝ) (L : Matrix S S ℝ) (J : Finset ℝ≥0)
    (states : J → S) :
    finiteTimeLaw p L J {states} =
      ENNReal.ofReal
        (finChainWeight (evolvedEntrance p L) (generatorKernel L)
          (orderedTimes J) ((orderedStateEquiv J).symm states)) := by
  rw [finiteTimeLaw, MeasureTheory.Measure.map_apply
    (measurable_of_finite (orderedStateEquiv J))
    (MeasurableSet.singleton states)]
  have hpreimage :
      (orderedStateEquiv J : (Fin J.card → S) → (J → S)) ⁻¹' {states} =
        {(orderedStateEquiv J).symm states} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (orderedStateEquiv J).apply_eq_iff_eq_symm_apply
  rw [hpreimage]
  exact finChainLaw_apply_singleton
    (evolvedEntrance p L) (generatorKernel L) (orderedTimes J)
      ((orderedStateEquiv J).symm states)

/-- Every finite-set law is a probability measure. -/
theorem finiteTimeLaw_isProbabilityMeasure
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (J : Finset ℝ≥0) :
    MeasureTheory.IsProbabilityMeasure (finiteTimeLaw p L J) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (evolvedGeneratorFinChainLaw p L (orderedTimes J)) :=
    evolvedGeneratorFinChainLaw_isProbabilityMeasure p hp hp_sum L hL
      (orderedTimes J) (orderedTimes_monotone J)
      (orderedTimes_nonnegative J)
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    (measurable_of_finite (orderedStateEquiv J)).aemeasurable

/-- Adding one new observation time and then restricting back to the old
finite set recovers the old finite-dimensional law exactly. -/
theorem finiteTimeLaw_insert_projective
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (J : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∉ J) :
    finiteTimeLaw p L J =
      MeasureTheory.Measure.map
        (Finset.restrict₂ (π := fun _ : ℝ≥0 => S)
          (Finset.subset_insert t J))
        (finiteTimeLaw p L (insert t J)) := by
  let I : Finset ℝ≥0 := insert t J
  have hcard : I.card = J.card + 1 := by simp [I, ht]
  let q : Fin (J.card + 1) :=
    (I.orderIsoOfFin hcard).symm ⟨t, by simp [I]⟩
  let timesI := orderedTimesWithCard I hcard
  let tupleLawI := evolvedGeneratorFinChainLaw p L timesI
  have htimes : q.removeNth timesI = orderedTimes J := by
    simpa [I, hcard, q, timesI] using
      (removeNth_orderedTimesWithCard_insert J t ht)
  have hproj :
      evolvedGeneratorFinChainLaw p L (orderedTimes J) =
        MeasureTheory.Measure.map (q.removeNth ·) tupleLawI := by
    rw [← htimes]
    exact evolvedGeneratorFinChainLaw_map_removeNth
      p hp hp_sum L hL timesI
      (orderedTimesWithCard_monotone I hcard)
      (orderedTimesWithCard_nonnegative I hcard) q
  have hJI : J ⊆ I := by simp [I]
  have hcomm :
      (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI) ∘
          orderedStateEquivWithCard I hcard =
        orderedStateEquiv J ∘ (q.removeNth ·) := by
    funext states
    simpa [I, hcard, q] using
      (restrict_orderedStateEquivWithCard_insert J t ht states)
  change finiteTimeLaw p L J =
    MeasureTheory.Measure.map
      (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI)
      (finiteTimeLaw p L I)
  calc
    finiteTimeLaw p L J =
        MeasureTheory.Measure.map (orderedStateEquiv J)
          (evolvedGeneratorFinChainLaw p L (orderedTimes J)) := rfl
    _ = MeasureTheory.Measure.map (orderedStateEquiv J)
          (MeasureTheory.Measure.map (q.removeNth ·) tupleLawI) := by
      rw [hproj]
    _ = MeasureTheory.Measure.map
          (orderedStateEquiv J ∘ (q.removeNth ·)) tupleLawI :=
      MeasureTheory.Measure.map_map
        (measurable_of_finite (orderedStateEquiv J))
        (measurable_of_finite (q.removeNth ·))
    _ = MeasureTheory.Measure.map
          ((Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI) ∘
            orderedStateEquivWithCard I hcard) tupleLawI := by
      rw [hcomm]
    _ = MeasureTheory.Measure.map
          (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI)
          (MeasureTheory.Measure.map
            (orderedStateEquivWithCard I hcard) tupleLawI) :=
      (MeasureTheory.Measure.map_map
        (measurable_of_finite
          (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI))
        (measurable_of_finite
          (orderedStateEquivWithCard I hcard))).symm
    _ = MeasureTheory.Measure.map
          (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI)
          (finiteTimeLaw p L I) := by
      change MeasureTheory.Measure.map
          (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI)
          (finiteTimeLawWithCard p L I hcard) =
        MeasureTheory.Measure.map
          (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI)
          (finiteTimeLaw p L I)
      rw [finiteTimeLawWithCard_eq p L I hcard]

/-- Transporting the larger index finset along an equality does not change
the restricted finite-time law.  Equality elimination handles the dependent
subtype function spaces hidden in the two measures. -/
theorem map_restrict_finiteTimeLaw_congr
    (p : S → ℝ) (L : Matrix S S ℝ)
    {J I I' : Finset ℝ≥0} (hJI : J ⊆ I) (hJI' : J ⊆ I')
    (hII' : I = I') :
    MeasureTheory.Measure.map
        (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI)
        (finiteTimeLaw p L I) =
      MeasureTheory.Measure.map
        (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI')
        (finiteTimeLaw p L I') := by
  subst I'
  rfl

/-- Projectivity when the larger finite time set is presented as a disjoint
union.  The proof iterates the exact one-point marginalization theorem. -/
theorem finiteTimeLaw_union_projective
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (J D : Finset ℝ≥0) (hdisj : Disjoint J D) :
    finiteTimeLaw p L J =
      MeasureTheory.Measure.map
        (Finset.restrict₂ (π := fun _ : ℝ≥0 => S)
          (Finset.subset_union_left))
        (finiteTimeLaw p L (J ∪ D)) := by
  classical
  induction D using Finset.induction_on with
  | empty =>
      have hid :
          Finset.restrict₂ (π := fun _ : ℝ≥0 => S)
              (show J ⊆ J by exact Finset.Subset.rfl) = id := by
        funext states j
        rfl
      have hbase : finiteTimeLaw p L J =
          MeasureTheory.Measure.map
            (Finset.restrict₂ (π := fun _ : ℝ≥0 => S)
              (show J ⊆ J by exact Finset.Subset.rfl))
            (finiteTimeLaw p L J) := by
        rw [hid, MeasureTheory.Measure.map_id]
      exact hbase.trans (map_restrict_finiteTimeLaw_congr p L
        (show J ⊆ J by exact Finset.Subset.rfl)
        Finset.subset_union_left (by simp))
  | @insert t D ht ih =>
      have htJ : t ∉ J := by
        intro htJ
        exact (Finset.disjoint_left.mp hdisj) htJ (by simp)
      have hdisjJD : Disjoint J D :=
        hdisj.mono_right (Finset.subset_insert t D)
      have hind := ih hdisjJD
      let K : Finset ℝ≥0 := J ∪ D
      have htK : t ∉ K := by simp [K, ht, htJ]
      have hstep := finiteTimeLaw_insert_projective
        p hp hp_sum L hL K t htK
      have hJK : J ⊆ K := by simp [K]
      have hKI : K ⊆ insert t K := Finset.subset_insert t K
      have hJI : J ⊆ insert t K := hJK.trans hKI
      have hcalc : finiteTimeLaw p L J =
          MeasureTheory.Measure.map
            (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI)
            (finiteTimeLaw p L (insert t K)) := by
        calc
          finiteTimeLaw p L J =
              MeasureTheory.Measure.map
                (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJK)
                (finiteTimeLaw p L K) := by
            simpa [K] using hind
          _ = MeasureTheory.Measure.map
                (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJK)
                (MeasureTheory.Measure.map
                  (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hKI)
                  (finiteTimeLaw p L (insert t K))) := by
            rw [hstep]
          _ = MeasureTheory.Measure.map
                ((Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJK) ∘
                  Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hKI)
                (finiteTimeLaw p L (insert t K)) :=
            MeasureTheory.Measure.map_map
              (measurable_of_finite
                (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJK))
              (measurable_of_finite
                (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hKI))
          _ = MeasureTheory.Measure.map
                (Finset.restrict₂ (π := fun _ : ℝ≥0 => S) hJI)
                (finiteTimeLaw p L (insert t K)) := by
            congr 1
      exact hcalc.trans (map_restrict_finiteTimeLaw_congr p L hJI
        Finset.subset_union_left (by simp [K]))

/-- The chronologically defined finite-generator laws form a genuine
projective family over all finite subsets of nonnegative real time. -/
theorem finiteTimeLaw_isProjectiveMeasureFamily
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L) :
    @MeasureTheory.IsProjectiveMeasureFamily ℝ≥0 (fun _ => S)
      (fun _ => inferInstance) (finiteTimeLaw p L) := by
  intro I J hJI
  have hdisj : Disjoint J (I \ J) := by
    refine Finset.disjoint_left.mpr ?_
    intro a haJ haDiff
    exact (Finset.mem_sdiff.mp haDiff).2 haJ
  have h := finiteTimeLaw_union_projective
    p hp hp_sum L hL J (I \ J) hdisj
  exact h.trans (map_restrict_finiteTimeLaw_congr p L
    Finset.subset_union_left hJI
    (Finset.union_sdiff_of_subset hJI))

/-- Every finite-state generator with a nonnegative normalized entrance law
has a genuine probability law on the full nonnegative-real-time coordinate
process, and all of its finite marginals are the chronological Markov laws
constructed above. -/
theorem exists_generator_process_measure
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L) :
    ∃ μ : MeasureTheory.Measure (ℝ≥0 → S),
      MeasureTheory.IsProbabilityMeasure μ ∧
      MeasureTheory.IsProjectiveLimit μ (finiteTimeLaw p L) := by
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  letI : CompactSpace S := inferInstance
  letI (J : Finset ℝ≥0) :
      MeasureTheory.IsProbabilityMeasure (finiteTimeLaw p L J) :=
    finiteTimeLaw_isProbabilityMeasure p hp hp_sum L hL J
  exact NCG.FiniteStateProjectiveLimit.exists_probability_projectiveLimit
    (ι := ℝ≥0) (X := fun _ : ℝ≥0 => S)
    (P := finiteTimeLaw p L)
    (finiteTimeLaw_isProjectiveMeasureFamily p hp hp_sum L hL)

end NCG.FiniteGeneratorProjectiveFamily
